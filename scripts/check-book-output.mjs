#!/usr/bin/env node
// Checks the generated pages of the book, which `lake build` cannot see:
//
// - Every formula compiles under the KaTeX bundled with the site. The site itself renders with
//   `throwOnError: false`, so a bad formula would otherwise show up as red text in production.
// - Every local link and asset resolves, including `#fragment`s. This matters because the site is
//   served from a subdirectory on GitHub Pages, so a root-relative URL would break there only.
//
// Usage: node scripts/check-book-output.mjs _out/book/html-multi

import { readFileSync, readdirSync, statSync, existsSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, relative, resolve } from "node:path";

const site = resolve(process.argv[2] ?? "_out/book/html-multi");
const katex = createRequire(import.meta.url)(join(site, "-verso-data/katex/katex.js"));

const decode = (s) =>
  s.replace(/&(lt|gt|quot|apos|amp|#x?[0-9a-fA-F]+);/g, (_, e) => {
    if (e[0] === "#") {
      const hex = e[1] === "x";
      return String.fromCodePoint(parseInt(e.slice(hex ? 2 : 1), hex ? 16 : 10));
    }
    return { lt: "<", gt: ">", quot: '"', apos: "'", amp: "&" }[e];
  });

const pages = [];
const walk = (dir) => {
  for (const name of readdirSync(dir)) {
    const path = join(dir, name);
    if (statSync(path).isDirectory()) walk(path);
    else if (name.endsWith(".html")) pages.push(path);
  }
};
walk(site);

const errors = [];
const sources = new Map(pages.map((p) => [p, readFileSync(p, "utf8")]));
const fileOf = (path) => {
  if (existsSync(path) && statSync(path).isFile()) return path;
  const index = join(path, "index.html");
  return existsSync(index) ? index : null;
};

let formulas = 0;
let links = 0;
for (const [page, html] of sources) {
  const rel = relative(site, page);

  for (const [, mode, tex] of html.matchAll(/<code class="math (inline|display)">([^<]*)<\/code>/g)) {
    formulas += 1;
    try {
      katex.renderToString(decode(tex), {
        displayMode: mode === "display",
        throwOnError: true,
        strict: "error",
      });
    } catch (e) {
      errors.push(`${rel}: formula does not compile: ${decode(tex)}\n  ${e.message}`);
    }
  }

  const base = html.match(/<base href="([^"]*)"/)?.[1] ?? "./";
  if (!base.startsWith(".")) errors.push(`${rel}: the base URL ${base} is not relative`);
  const baseDir = resolve(dirname(page), base);

  // The bodies of inline scripts contain text that only looks like tags.
  const markup = html.replace(/(<script\b[^>]*>)[\s\S]*?<\/script>/g, "$1</script>");
  for (const [, url] of markup.matchAll(/<(?:a|link|script|img)\b[^>]*?\b(?:href|src)="([^"]*)"/g)) {
    const target = decode(url);
    if (/^[a-z]+:|^\/\//i.test(target) || target === "#" || target === "") continue;
    links += 1;
    if (target.startsWith("/")) {
      errors.push(`${rel}: root-relative URL, which breaks under a subdirectory: ${target}`);
      continue;
    }
    const [pathAndQuery, fragment] = target.split("#");
    const path = pathAndQuery.split("?")[0];
    const file = path === "" ? page : fileOf(resolve(baseDir, path));
    if (file === null) {
      errors.push(`${rel}: broken link: ${target}`);
    } else if (fragment && file.endsWith(".html")) {
      const contents = sources.get(file) ?? readFileSync(file, "utf8");
      if (!contents.includes(`id="${fragment}"`)) {
        errors.push(`${rel}: link to a missing anchor: ${target}`);
      }
    }
  }
}

if (formulas === 0) errors.push("no formulas found: the extraction in this script is out of date");
if (links === 0) errors.push("no links found: the extraction in this script is out of date");

for (const e of errors) console.error(e);
console.log(`${pages.length} pages, ${formulas} formulas, ${links} local links: ${errors.length} errors`);
process.exit(errors.length === 0 ? 0 : 1);
