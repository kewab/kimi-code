import { spawn } from "child_process";
import { readdirSync, realpathSync, statSync } from "fs";
import { homedir } from "os";
import { basename, dirname, join } from "path";
import { fuzzyFilter, fuzzyMatch, fuzzyQueryVariants } from "./fuzzy.ts";

const PATH_DELIMITERS = new Set([" ", "\t", '"', "'", "="]);
const SEPARATOR_PATTERN = "[\\\\/]";
const ROOT_SEPARATOR_PATTERN = `${SEPARATOR_PATTERN}+`;
const FUZZY_MIN_QUERY_LENGTH = 2;
const FUZZY_TOP_K = 20;
const FD_MAX_RESULTS = 5000;

function toDisplayPath(value: string): string {
	return value.replace(/\\/g, "/");
}

function escapeRegex(value: string): string {
	return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function buildFdPathQuery(query: string): string {
	const normalized = toDisplayPath(query);
	if (!normalized.includes("/")) {
		return normalized;
	}

	const hasTrailingSeparator = normalized.endsWith("/");
	const trimmed = normalized.replace(/^\/+|\/+$/g, "");
	if (!trimmed) {
		return normalized;
	}

	const segments = trimmed
		.split("/")
		.filter(Boolean)
		.map((segment) => escapeRegex(segment));
	if (segments.length === 0) {
		return normalized;
	}

	let pattern = segments.join(SEPARATOR_PATTERN);
	if (hasTrailingSeparator) {
		pattern += SEPARATOR_PATTERN;
	}
	return pattern;
}

// How fd should be invoked for one search. Separating the spec from the spawn
// lets the caller run a precise and a fuzzy pass against the same base dir.
type FdSearchSpec = {
	pattern: string | null;
	fullPath: boolean;
	ignoreCase: boolean;
};

function buildFdPreciseSearch(query: string): FdSearchSpec {
	return {
		pattern: query ? buildFdPathQuery(query) : null,
		fullPath: toDisplayPath(query).includes("/"),
		ignoreCase: false,
	};
}

// A slash-free query can still name a path through its segments ("aabc" ->
// "aa/bb/cc.go"), which the basename-only precise pass never sees. Leading dots
// and tildes are left to the precise pass so path-scoped input keeps its
// existing meaning.
function shouldSearchPathFuzzy(query: string): boolean {
	const normalized = toDisplayPath(query);
	return (
		normalized.length >= FUZZY_MIN_QUERY_LENGTH &&
		!normalized.includes("/") &&
		!normalized.startsWith(".") &&
		!normalized.startsWith("~")
	);
}

// fd matches --full-path patterns against the canonical absolute path, so the
// pattern is anchored to the canonical base dir: an unanchored subsequence would
// match the machine path prefix and exhaust --max-results before fd reaches real
// matches. The ".*" after the anchor keeps the subsequence free to start at any
// depth below the base, and -i is required because the anchor carries the
// machine's casing (e.g. /Users), which flips fd's smart-case to case-sensitive.
// The leading separator is a run so UNC roots (//server/share/...) anchor too,
// and the alternatives mirror fuzzyQueryVariants so fd admits every spelling the
// scorer accepts.
function buildFdFuzzySearch(query: string, baseDir: string): FdSearchSpec | null {
	let canonicalBase: string;
	try {
		canonicalBase = toDisplayPath(realpathSync(baseDir));
	} catch {
		return null;
	}

	const drivePrefix = /^([A-Za-z]:)/.exec(canonicalBase)?.[1];
	const pathPart = drivePrefix ? canonicalBase.slice(drivePrefix.length) : canonicalBase;
	const anchorSegments = pathPart
		.split("/")
		.filter(Boolean)
		.map((segment) => escapeRegex(segment));
	const anchor = `^(?:[A-Za-z]:)?${ROOT_SEPARATOR_PATTERN}${anchorSegments.join(SEPARATOR_PATTERN)}`;
	const buildSubsequence = (variant: string): string =>
		[...variant].map((char) => escapeRegex(char)).join(".*");
	const [primaryVariant, swappedVariant] = fuzzyQueryVariants(toDisplayPath(query));
	const subsequence = swappedVariant
		? `(?:${buildSubsequence(primaryVariant)}|${buildSubsequence(swappedVariant)})`
		: buildSubsequence(primaryVariant);

	return {
		pattern: `${anchor}.*${subsequence}`,
		fullPath: true,
		ignoreCase: true,
	};
}

function findLastDelimiter(text: string): number {
	for (let i = text.length - 1; i >= 0; i -= 1) {
		if (PATH_DELIMITERS.has(text[i] ?? "")) {
			return i;
		}
	}
	return -1;
}

function findUnclosedQuoteStart(text: string): number | null {
	let inQuotes = false;
	let quoteStart = -1;

	for (let i = 0; i < text.length; i += 1) {
		if (text[i] === '"') {
			inQuotes = !inQuotes;
			if (inQuotes) {
				quoteStart = i;
			}
		}
	}

	return inQuotes ? quoteStart : null;
}

function isTokenStart(text: string, index: number): boolean {
	return index === 0 || PATH_DELIMITERS.has(text[index - 1] ?? "");
}

function extractQuotedPrefix(text: string): string | null {
	const quoteStart = findUnclosedQuoteStart(text);
	if (quoteStart === null) {
		return null;
	}

	if (quoteStart > 0 && text[quoteStart - 1] === "@") {
		if (!isTokenStart(text, quoteStart - 1)) {
			return null;
		}
		return text.slice(quoteStart - 1);
	}

	if (!isTokenStart(text, quoteStart)) {
		return null;
	}

	return text.slice(quoteStart);
}

function parsePathPrefix(prefix: string): { rawPrefix: string; isAtPrefix: boolean; isQuotedPrefix: boolean } {
	if (prefix.startsWith('@"')) {
		return { rawPrefix: prefix.slice(2), isAtPrefix: true, isQuotedPrefix: true };
	}
	if (prefix.startsWith('"')) {
		return { rawPrefix: prefix.slice(1), isAtPrefix: false, isQuotedPrefix: true };
	}
	if (prefix.startsWith("@")) {
		return { rawPrefix: prefix.slice(1), isAtPrefix: true, isQuotedPrefix: false };
	}
	return { rawPrefix: prefix, isAtPrefix: false, isQuotedPrefix: false };
}

function buildCompletionValue(
	path: string,
	options: { isDirectory: boolean; isAtPrefix: boolean; isQuotedPrefix: boolean },
): string {
	const needsQuotes = options.isQuotedPrefix || path.includes(" ");
	const prefix = options.isAtPrefix ? "@" : "";

	if (!needsQuotes) {
		return `${prefix}${path}`;
	}

	const openQuote = `${prefix}"`;
	const closeQuote = '"';
	return `${openQuote}${path}${closeQuote}`;
}

// Use fd to walk directory tree (fast, respects .gitignore)
async function walkDirectoryWithFd(
	baseDir: string,
	fdPath: string,
	search: FdSearchSpec,
	maxResults: number | undefined,
	signal: AbortSignal,
	onEntry?: (entry: { path: string; isDirectory: boolean }) => void,
): Promise<Array<{ path: string; isDirectory: boolean }>> {
	const args = [
		"--base-directory",
		baseDir,
		"--type",
		"f",
		"--type",
		"d",
		"--follow",
		"--hidden",
		"--exclude",
		".git",
		"--exclude",
		".git/*",
		"--exclude",
		".git/**",
	];
	if (maxResults !== undefined) {
		args.splice(2, 0, "--max-results", String(maxResults));
	}

	if (search.fullPath) {
		args.push("--full-path");
	}

	if (search.ignoreCase) {
		args.push("--ignore-case");
	}

	if (search.pattern) {
		args.push(search.pattern);
	}

	return await new Promise((resolve) => {
		if (signal.aborted) {
			resolve([]);
			return;
		}

		const child = spawn(fdPath, args, {
			stdio: ["ignore", "pipe", "pipe"],
		});
		let stdout = "";
		let pendingLine = "";
		let resolved = false;

		const finish = (results: Array<{ path: string; isDirectory: boolean }>) => {
			if (resolved) return;
			resolved = true;
			signal.removeEventListener("abort", onAbort);
			resolve(results);
		};

		const onAbort = () => {
			if (child.exitCode === null) {
				child.kill("SIGKILL");
			}
		};

		signal.addEventListener("abort", onAbort, { once: true });
		child.stdout.setEncoding("utf-8");
		const consumeLine = (line: string) => {
			const displayLine = toDisplayPath(line);
			const hasTrailingSeparator = displayLine.endsWith("/");
			const normalizedPath = hasTrailingSeparator ? displayLine.slice(0, -1) : displayLine;
			if (!normalizedPath || normalizedPath === ".git" || normalizedPath.startsWith(".git/") || normalizedPath.includes("/.git/")) {
				return;
			}
			onEntry?.({ path: displayLine, isDirectory: hasTrailingSeparator });
		};
		child.stdout.on("data", (chunk: string) => {
			if (onEntry) {
				pendingLine += chunk;
				const lines = pendingLine.split("\n");
				pendingLine = lines.pop() ?? "";
				for (const line of lines) {
					if (line) consumeLine(line);
				}
			} else {
				stdout += chunk;
			}
		});
		child.on("error", () => {
			finish([]);
		});
		child.on("close", (code) => {
			if (onEntry && pendingLine) consumeLine(pendingLine);
			if (signal.aborted || code !== 0 || (!onEntry && !stdout)) {
				finish([]);
				return;
			}
			if (onEntry) {
				finish([]);
				return;
			}

			const lines = stdout.trim().split("\n").filter(Boolean);
			const results: Array<{ path: string; isDirectory: boolean }> = [];

			for (const line of lines) {
				const displayLine = toDisplayPath(line);
				const hasTrailingSeparator = displayLine.endsWith("/");
				const normalizedPath = hasTrailingSeparator ? displayLine.slice(0, -1) : displayLine;
				if (normalizedPath && normalizedPath !== ".git" && !normalizedPath.startsWith(".git/") && !normalizedPath.includes("/.git/")) {
					results.push({ path: displayLine, isDirectory: hasTrailingSeparator });
				}
			}

			finish(results);
		});
	});
}

export interface AutocompleteItem {
	value: string;
	label: string;
	description?: string;
	/** Provider-specific metadata forwarded unchanged to applyCompletion. */
	data?: Record<string, unknown>;
}

type Awaitable<T> = T | Promise<T>;

export interface SlashCommand {
	name: string;
	description?: string;
	argumentHint?: string;
	// Function to get argument completions for this command
	// Returns null if no argument completion is available
	getArgumentCompletions?(argumentPrefix: string): Awaitable<AutocompleteItem[] | null>;
}

export interface AutocompleteSuggestions {
	items: AutocompleteItem[];
	prefix: string; // What we're matching against (e.g., "/" or "src/")
}

export interface AutocompleteProvider {
	/** Characters that should naturally trigger this provider at token boundaries. */
	triggerCharacters?: string[];

	// Get autocomplete suggestions for current text/cursor position
	// Returns null if no suggestions available
	getSuggestions(
		lines: string[],
		cursorLine: number,
		cursorCol: number,
		options: { signal: AbortSignal; force?: boolean },
	): Promise<AutocompleteSuggestions | null>;

	// Apply the selected item
	// Returns the new text and cursor position
	applyCompletion(
		lines: string[],
		cursorLine: number,
		cursorCol: number,
		item: AutocompleteItem,
		prefix: string,
	): {
		lines: string[];
		cursorLine: number;
		cursorCol: number;
	};

	// Check if file completion should trigger for explicit Tab completion
	shouldTriggerFileCompletion?(lines: string[], cursorLine: number, cursorCol: number): boolean;
}

// Combined provider that handles both slash commands and file paths
export class CombinedAutocompleteProvider implements AutocompleteProvider {
	private commands: (SlashCommand | AutocompleteItem)[];
	private basePath: string;
	private additionalBasePaths: string[];
	private fdPath: string | null;

	constructor(
		commands: (SlashCommand | AutocompleteItem)[] = [],
		basePath: string,
		fdPath: string | null = null,
		additionalBasePaths: readonly string[] = [],
	) {
		this.commands = commands;
		this.basePath = basePath;
		this.additionalBasePaths = additionalBasePaths.map((p) => toDisplayPath(p));
		this.fdPath = fdPath;
	}

	async getSuggestions(
		lines: string[],
		cursorLine: number,
		cursorCol: number,
		options: { signal: AbortSignal; force?: boolean },
	): Promise<AutocompleteSuggestions | null> {
		const currentLine = lines[cursorLine] || "";
		const textBeforeCursor = currentLine.slice(0, cursorCol);

		const atPrefix = this.extractAtPrefix(textBeforeCursor);
		if (atPrefix) {
			const { rawPrefix, isQuotedPrefix } = parsePathPrefix(atPrefix);
			const suggestions = await this.getFuzzyFileSuggestions(rawPrefix, {
				isQuotedPrefix,
				signal: options.signal,
			});
			if (suggestions.length === 0) return null;

			return {
				items: suggestions,
				prefix: atPrefix,
			};
		}

		if (!options.force && textBeforeCursor.startsWith("/")) {
			const spaceIndex = textBeforeCursor.indexOf(" ");

			if (spaceIndex === -1) {
				const prefix = textBeforeCursor.slice(1);
				const commandItems = this.commands.map((cmd) => {
					const name = "name" in cmd ? cmd.name : cmd.value;
					const hint = "argumentHint" in cmd && cmd.argumentHint ? cmd.argumentHint : undefined;
					const desc = cmd.description ?? "";
					const fullDesc = hint ? (desc ? `${hint} — ${desc}` : hint) : desc;
					return {
						name,
						label: name,
						description: fullDesc || undefined,
					};
				});

				const filtered = fuzzyFilter(commandItems, prefix, (item) => item.name).map((item) => ({
					value: item.name,
					label: item.label,
					...(item.description && { description: item.description }),
				}));

				if (filtered.length === 0) return null;

				return {
					items: filtered,
					prefix: textBeforeCursor,
				};
			}

			const commandName = textBeforeCursor.slice(1, spaceIndex);
			const argumentText = textBeforeCursor.slice(spaceIndex + 1);

			const command = this.commands.find((cmd) => {
				const name = "name" in cmd ? cmd.name : cmd.value;
				return name === commandName;
			});
			if (!command || !("getArgumentCompletions" in command) || !command.getArgumentCompletions) {
				return null;
			}

			const argumentSuggestions = await command.getArgumentCompletions(argumentText);
			if (!Array.isArray(argumentSuggestions) || argumentSuggestions.length === 0) {
				return null;
			}

			return {
				items: argumentSuggestions,
				prefix: argumentText,
			};
		}

		const pathMatch = this.extractPathPrefix(textBeforeCursor, options.force ?? false);
		if (pathMatch === null) {
			return null;
		}

		const suggestions = this.getFileSuggestions(pathMatch);
		if (suggestions.length === 0) return null;

		return {
			items: suggestions,
			prefix: pathMatch,
		};
	}

	applyCompletion(
		lines: string[],
		cursorLine: number,
		cursorCol: number,
		item: AutocompleteItem,
		prefix: string,
	): { lines: string[]; cursorLine: number; cursorCol: number } {
		const currentLine = lines[cursorLine] || "";
		const beforePrefix = currentLine.slice(0, cursorCol - prefix.length);
		const afterCursor = currentLine.slice(cursorCol);
		const isQuotedPrefix = prefix.startsWith('"') || prefix.startsWith('@"');
		const hasLeadingQuoteAfterCursor = afterCursor.startsWith('"');
		const hasTrailingQuoteInItem = item.value.endsWith('"');
		const adjustedAfterCursor =
			isQuotedPrefix && hasTrailingQuoteInItem && hasLeadingQuoteAfterCursor ? afterCursor.slice(1) : afterCursor;

		// Check if we're completing a slash command (prefix starts with "/" but NOT a file path)
		// Slash commands are at the start of the line and don't contain path separators after the first /
		const isSlashCommand = prefix.startsWith("/") && beforePrefix.trim() === "" && !prefix.slice(1).includes("/");
		if (isSlashCommand) {
			// This is a command name completion
			const newLine = `${beforePrefix}/${item.value} ${adjustedAfterCursor}`;
			const newLines = [...lines];
			newLines[cursorLine] = newLine;

			return {
				lines: newLines,
				cursorLine,
				cursorCol: beforePrefix.length + item.value.length + 2, // +2 for "/" and space
			};
		}

		// Check if we're completing a file attachment (prefix starts with "@")
		if (prefix.startsWith("@")) {
			// This is a file attachment completion
			// Don't add space after directories so user can continue autocompleting
			const isDirectory = item.label.endsWith("/");
			const suffix = isDirectory ? "" : " ";
			const newLine = `${beforePrefix + item.value}${suffix}${adjustedAfterCursor}`;
			const newLines = [...lines];
			newLines[cursorLine] = newLine;

			const hasTrailingQuote = item.value.endsWith('"');
			const cursorOffset = isDirectory && hasTrailingQuote ? item.value.length - 1 : item.value.length;

			return {
				lines: newLines,
				cursorLine,
				cursorCol: beforePrefix.length + cursorOffset + suffix.length,
			};
		}

		// Check if we're in a slash command context (beforePrefix contains "/command ")
		const textBeforeCursor = currentLine.slice(0, cursorCol);
		if (textBeforeCursor.includes("/") && textBeforeCursor.includes(" ")) {
			// This is likely a command argument completion
			const newLine = beforePrefix + item.value + adjustedAfterCursor;
			const newLines = [...lines];
			newLines[cursorLine] = newLine;

			const isDirectory = item.label.endsWith("/");
			const hasTrailingQuote = item.value.endsWith('"');
			const cursorOffset = isDirectory && hasTrailingQuote ? item.value.length - 1 : item.value.length;

			return {
				lines: newLines,
				cursorLine,
				cursorCol: beforePrefix.length + cursorOffset,
			};
		}

		// For file paths, complete the path
		const newLine = beforePrefix + item.value + adjustedAfterCursor;
		const newLines = [...lines];
		newLines[cursorLine] = newLine;

		const isDirectory = item.label.endsWith("/");
		const hasTrailingQuote = item.value.endsWith('"');
		const cursorOffset = isDirectory && hasTrailingQuote ? item.value.length - 1 : item.value.length;

		return {
			lines: newLines,
			cursorLine,
			cursorCol: beforePrefix.length + cursorOffset,
		};
	}

	// Extract @ prefix for fuzzy file suggestions
	private extractAtPrefix(text: string): string | null {
		const quotedPrefix = extractQuotedPrefix(text);
		if (quotedPrefix?.startsWith('@"')) {
			return quotedPrefix;
		}

		const lastDelimiterIndex = findLastDelimiter(text);
		const tokenStart = lastDelimiterIndex === -1 ? 0 : lastDelimiterIndex + 1;

		if (text[tokenStart] === "@") {
			return text.slice(tokenStart);
		}

		return null;
	}

	// Extract a path-like prefix from the text before cursor
	private extractPathPrefix(text: string, forceExtract: boolean = false): string | null {
		const quotedPrefix = extractQuotedPrefix(text);
		if (quotedPrefix) {
			return quotedPrefix;
		}

		const lastDelimiterIndex = findLastDelimiter(text);
		const pathPrefix = lastDelimiterIndex === -1 ? text : text.slice(lastDelimiterIndex + 1);

		// For forced extraction (Tab key), always return something
		if (forceExtract) {
			return pathPrefix;
		}

		// For natural triggers, return if it looks like a path, ends with /, starts with ~/, .
		// Only return empty string if the text looks like it's starting a path context
		if (pathPrefix.includes("/") || pathPrefix.startsWith(".") || pathPrefix.startsWith("~/")) {
			return pathPrefix;
		}

		// Return empty string only after a space (not for completely empty text)
		// Empty text should not trigger file suggestions - that's for forced Tab completion
		if (pathPrefix === "" && text.endsWith(" ")) {
			return pathPrefix;
		}

		return null;
	}

	// Expand home directory (~/) to actual home path
	private expandHomePath(path: string): string {
		if (path.startsWith("~/")) {
			const expandedPath = join(homedir(), path.slice(2));
			// Preserve trailing slash if original path had one
			return path.endsWith("/") && !expandedPath.endsWith("/") ? `${expandedPath}/` : expandedPath;
		} else if (path === "~") {
			return homedir();
		}
		return path;
	}

	private searchRoots(): string[] {
		const seen = new Set<string>();
		const roots: string[] = [];
		for (const root of [this.basePath, ...this.additionalBasePaths]) {
			const key = toDisplayPath(root);
			if (seen.has(key)) continue;
			seen.add(key);
			roots.push(root);
		}
		return roots;
	}

	private resolveScopedFuzzyQuery(
		rawQuery: string,
	):
		| { kind: "relative"; displayBase: string; query: string }
		| { kind: "absolute"; baseDir: string; displayBase: string; query: string }
		| null {
		const normalizedQuery = toDisplayPath(rawQuery);
		const slashIndex = normalizedQuery.lastIndexOf("/");
		if (slashIndex === -1) {
			return null;
		}

		const displayBase = normalizedQuery.slice(0, slashIndex + 1);
		const query = normalizedQuery.slice(slashIndex + 1);

		// Absolute (~/, /) scopes resolve to a single existing directory and do
		// not fan out across additional roots. Relative scopes are expanded per
		// search root by the caller.
		if (displayBase.startsWith("~/") || displayBase.startsWith("/")) {
			const baseDir = displayBase.startsWith("~/") ? this.expandHomePath(displayBase) : displayBase;
			try {
				if (!statSync(baseDir).isDirectory()) {
					return null;
				}
			} catch {
				return null;
			}
			return { kind: "absolute", baseDir, displayBase, query };
		}

		return { kind: "relative", displayBase, query };
	}

	private scopedPathForDisplay(displayBase: string, relativePath: string): string {
		const normalizedRelativePath = toDisplayPath(relativePath);
		if (displayBase === "/") {
			return `/${normalizedRelativePath}`;
		}
		return `${toDisplayPath(displayBase)}${normalizedRelativePath}`;
	}

	// Get file/directory suggestions for a given path prefix
	private getFileSuggestions(prefix: string): AutocompleteItem[] {
		try {
			let searchDir: string;
			let searchPrefix: string;
			const { rawPrefix, isAtPrefix, isQuotedPrefix } = parsePathPrefix(prefix);
			let expandedPrefix = rawPrefix;

			// Handle home directory expansion
			if (expandedPrefix.startsWith("~")) {
				expandedPrefix = this.expandHomePath(expandedPrefix);
			}

			const isRootPrefix =
				rawPrefix === "" ||
				rawPrefix === "./" ||
				rawPrefix === "../" ||
				rawPrefix === "~" ||
				rawPrefix === "~/" ||
				rawPrefix === "/" ||
				(isAtPrefix && rawPrefix === "");

			if (isRootPrefix) {
				// Complete from specified position
				if (rawPrefix.startsWith("~") || expandedPrefix.startsWith("/")) {
					searchDir = expandedPrefix;
				} else {
					searchDir = join(this.basePath, expandedPrefix);
				}
				searchPrefix = "";
			} else if (rawPrefix.endsWith("/")) {
				// If prefix ends with /, show contents of that directory
				if (rawPrefix.startsWith("~") || expandedPrefix.startsWith("/")) {
					searchDir = expandedPrefix;
				} else {
					searchDir = join(this.basePath, expandedPrefix);
				}
				searchPrefix = "";
			} else {
				// Split into directory and file prefix
				const dir = dirname(expandedPrefix);
				const file = basename(expandedPrefix);
				if (rawPrefix.startsWith("~") || expandedPrefix.startsWith("/")) {
					searchDir = dir;
				} else {
					searchDir = join(this.basePath, dir);
				}
				searchPrefix = file;
			}

			const entries = readdirSync(searchDir, { withFileTypes: true });
			const suggestions: AutocompleteItem[] = [];

			for (const entry of entries) {
				if (!entry.name.toLowerCase().startsWith(searchPrefix.toLowerCase())) {
					continue;
				}

				// Check if entry is a directory (or a symlink pointing to a directory)
				let isDirectory = entry.isDirectory();
				if (!isDirectory && entry.isSymbolicLink()) {
					try {
						const fullPath = join(searchDir, entry.name);
						isDirectory = statSync(fullPath).isDirectory();
					} catch {
						// Broken symlink or permission error - treat as file
					}
				}

				let relativePath: string;
				const name = entry.name;
				const displayPrefix = rawPrefix;

				if (displayPrefix.endsWith("/")) {
					// If prefix ends with /, append entry to the prefix
					relativePath = displayPrefix + name;
				} else if (displayPrefix.includes("/") || displayPrefix.includes("\\")) {
					// Preserve ~/ format for home directory paths
					if (displayPrefix.startsWith("~/")) {
						const homeRelativeDir = displayPrefix.slice(2); // Remove ~/
						const dir = dirname(homeRelativeDir);
						relativePath = `~/${dir === "." ? name : join(dir, name)}`;
					} else if (displayPrefix.startsWith("/")) {
						// Absolute path - construct properly
						const dir = dirname(displayPrefix);
						if (dir === "/") {
							relativePath = `/${name}`;
						} else {
							relativePath = `${dir}/${name}`;
						}
					} else {
						relativePath = join(dirname(displayPrefix), name);
						// path.join normalizes away ./ prefix, preserve it
						if (displayPrefix.startsWith("./") && !relativePath.startsWith("./")) {
							relativePath = `./${relativePath}`;
						}
					}
				} else {
					// For standalone entries, preserve ~/ if original prefix was ~/
					if (displayPrefix.startsWith("~")) {
						relativePath = `~/${name}`;
					} else {
						relativePath = name;
					}
				}

				relativePath = toDisplayPath(relativePath);
				const pathValue = isDirectory ? `${relativePath}/` : relativePath;
				const value = buildCompletionValue(pathValue, {
					isDirectory,
					isAtPrefix,
					isQuotedPrefix,
				});

				suggestions.push({
					value,
					label: name + (isDirectory ? "/" : ""),
				});
			}

			// Sort directories first, then alphabetically
			suggestions.sort((a, b) => {
				const aIsDir = a.value.endsWith("/");
				const bIsDir = b.value.endsWith("/");
				if (aIsDir && !bIsDir) return -1;
				if (!aIsDir && bIsDir) return 1;
				return a.label.localeCompare(b.label);
			});

			return suggestions;
		} catch (_e) {
			// Directory doesn't exist or not accessible
			return [];
		}
	}

	// Score an entry against the query (higher = better match)
	// isDirectory adds bonus to prioritize folders
	private scoreEntry(filePath: string, query: string, isDirectory: boolean): number {
		const fileName = basename(filePath);
		const lowerFileName = fileName.toLowerCase();
		const lowerQuery = query.toLowerCase();

		let score = 0;

		// Exact filename match (highest)
		if (lowerFileName === lowerQuery) score = 100;
		// Filename starts with query
		else if (lowerFileName.startsWith(lowerQuery)) score = 80;
		// Substring match in filename
		else if (lowerFileName.includes(lowerQuery)) score = 50;
		// Substring match in full path
		else if (filePath.toLowerCase().includes(lowerQuery)) score = 30;
		// Subsequence match across the relative path. Kept below the substring
		// tiers: 10 plus the directory bonus stays under the 30 tier, so a fuzzy
		// hit never outranks a real substring hit.
		else if (fuzzyMatch(query, filePath).matches) score = 10;

		// Directories get a bonus to appear first
		if (isDirectory && score > 0) score += 10;

		return score;
	}

	// Fuzzy file search using fd (fast, respects .gitignore). Fans out across
	// every search root (cwd + additional dirs) so `@` completion covers all
	// roots while still pushing the query down to fd.
	private async getFuzzyFileSuggestions(
		query: string,
		options: { isQuotedPrefix: boolean; signal: AbortSignal },
	): Promise<AutocompleteItem[]> {
		const fdPath = this.fdPath;
		if (!fdPath || options.signal.aborted) {
			return [];
		}

		try {
			const scoped = this.resolveScopedFuzzyQuery(query);

			type RootTarget = {
				baseDir: string;
				pathRoot: string;
				displayBase: string;
				fdQuery: string;
				isAdditional: boolean;
				absolute: boolean;
			};
			const targets: RootTarget[] = [];

			const pushFullPathTarget = (root: string) => {
				// Whole-tree search for this root using the original query (which
				// contains "/", so fd runs in --full-path mode).
				targets.push({
					baseDir: root,
					pathRoot: root,
					displayBase: "",
					fdQuery: query,
					isAdditional: root !== this.basePath,
					absolute: false,
				});
			};

			if (scoped?.kind === "absolute") {
				targets.push({
					baseDir: scoped.baseDir,
					pathRoot: scoped.baseDir,
					displayBase: scoped.displayBase,
					fdQuery: scoped.query,
					isAdditional: false,
					absolute: true,
				});
			} else if (scoped?.kind === "relative") {
				for (const root of this.searchRoots()) {
					const baseDir = join(root, scoped.displayBase);
					let isDir = false;
					try {
						isDir = statSync(baseDir).isDirectory();
					} catch {
						isDir = false;
					}
					if (isDir) {
						targets.push({
							baseDir,
							pathRoot: root,
							displayBase: scoped.displayBase,
							fdQuery: scoped.query,
							isAdditional: root !== this.basePath,
							absolute: false,
						});
					} else {
						// This root does not have the scoped directory. Fall back to a
						// per-root full-path search so another root having the prefix
						// does not hide matches that only exist under this root.
						pushFullPathTarget(root);
					}
				}
			} else {
				for (const root of this.searchRoots()) {
					pushFullPathTarget(root);
				}
			}

			if (targets.length === 0) {
				return [];
			}

			const allowFuzzy = shouldSearchPathFuzzy(query);

			const perRoot = await Promise.all(
				targets.map(async (target) => {
					const fuzzySearch = allowFuzzy ? buildFdFuzzySearch(target.fdQuery, target.baseDir) : null;
					const fuzzyEntries: Array<{ path: string; isDirectory: boolean }> = [];
					const onFuzzyEntry = fuzzySearch
						? (entry: { path: string; isDirectory: boolean }) => {
							const score = this.scoreEntry(entry.path, target.fdQuery, entry.isDirectory);
							if (score <= 0) return;
							const fuzzyScore = fuzzyMatch(target.fdQuery, entry.path).score;
							fuzzyEntries.push(entry);
							fuzzyEntries.sort(
								(a, b) =>
									this.scoreEntry(b.path, target.fdQuery, b.isDirectory) -
										this.scoreEntry(a.path, target.fdQuery, a.isDirectory) ||
										fuzzyMatch(target.fdQuery, a.path).score - fuzzyMatch(target.fdQuery, b.path).score ||
										a.path.localeCompare(b.path),
							);
							if (fuzzyEntries.length > FUZZY_TOP_K) fuzzyEntries.pop();
						  }
						: undefined;
					const [precise, fuzzy] = await Promise.all([
						walkDirectoryWithFd(
							target.baseDir,
							fdPath,
							buildFdPreciseSearch(target.fdQuery),
							FD_MAX_RESULTS,
							options.signal,
						),
						fuzzySearch
							? walkDirectoryWithFd(target.baseDir, fdPath, fuzzySearch, undefined, options.signal, onFuzzyEntry)
							: Promise.resolve([]),
					]);
					return [...precise, ...fuzzyEntries, ...fuzzy].map((entry) => ({ entry, target }));
				}),
			);
			if (options.signal.aborted) {
				return [];
			}

			type Scored = {
				path: string;
				isDirectory: boolean;
				score: number;
				fuzzyScore: number;
				target: RootTarget;
				absPath: string;
			};
			const bestByAbs = new Map<string, Scored>();
			for (const group of perRoot) {
				for (const { entry, target } of group) {
					const score = target.fdQuery ? this.scoreEntry(entry.path, target.fdQuery, entry.isDirectory) : 1;
					if (score <= 0) continue;
					const fuzzyScore = target.fdQuery ? fuzzyMatch(target.fdQuery, entry.path).score : 0;
					const pathWithoutSlash = entry.isDirectory ? entry.path.slice(0, -1) : entry.path;
					const absPath = target.absolute
						? toDisplayPath(join(target.displayBase, pathWithoutSlash))
						: toDisplayPath(join(target.pathRoot, target.displayBase, pathWithoutSlash));
					const existing = bestByAbs.get(absPath);
					if (!existing || score > existing.score) {
						bestByAbs.set(absPath, {
							path: entry.path,
							isDirectory: entry.isDirectory,
							score,
							fuzzyScore,
							target,
							absPath,
						});
					}
				}
			}

			const scored = [...bestByAbs.values()];
			// fd 输出顺序不保证质量，统一在本地按匹配分数和路径排序后截取结果。
			scored.sort((a, b) => b.score - a.score || a.fuzzyScore - b.fuzzyScore || a.absPath.localeCompare(b.absPath));
			const topEntries = scored.slice(0, 20);

			const suggestions: AutocompleteItem[] = [];
			for (const item of topEntries) {
				const pathWithoutSlash = item.isDirectory ? item.path.slice(0, -1) : item.path;
				const entryName = basename(pathWithoutSlash);
				let displayPath: string;
				if (item.target.absolute) {
					displayPath = this.scopedPathForDisplay(item.target.displayBase, pathWithoutSlash);
				} else if (item.target.isAdditional) {
					displayPath = item.absPath;
				} else {
					displayPath = item.target.displayBase
						? this.scopedPathForDisplay(item.target.displayBase, pathWithoutSlash)
						: pathWithoutSlash;
				}
				const completionPath = item.isDirectory ? `${displayPath}/` : displayPath;
				const value = buildCompletionValue(completionPath, {
					isDirectory: item.isDirectory,
					isAtPrefix: true,
					isQuotedPrefix: options.isQuotedPrefix,
				});

				suggestions.push({
					value,
					label: entryName + (item.isDirectory ? "/" : ""),
					description: displayPath,
				});
			}

			return suggestions;
		} catch {
			return [];
		}
	}

	// Check if we should trigger file completion (called on Tab key)
	shouldTriggerFileCompletion(lines: string[], cursorLine: number, cursorCol: number): boolean {
		const currentLine = lines[cursorLine] || "";
		const textBeforeCursor = currentLine.slice(0, cursorCol);

		// Don't trigger if we're typing a slash command at the start of the line
		if (textBeforeCursor.trim().startsWith("/") && !textBeforeCursor.trim().includes(" ")) {
			return false;
		}

		return true;
	}
}
