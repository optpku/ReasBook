/* Lean syntax colors adapted from ReasBook Reviewer's highlightLean.
 * Apache-2.0. All source text is escaped and retained exactly.
 */
(function () {
  "use strict";
  const escapeHtml = (value) => String(value ?? "").replace(/[&<>"']/g, (char) => ({
    "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;"
  })[char]);
  function highlightLean(value) {
    const source = String(value ?? "");
    const keywords = new Set([
      "abbrev", "axiom", "by", "class", "def", "deriving", "else", "example", "extends",
      "forall", "fun", "if", "in", "inductive", "instance", "lemma", "let", "match",
      "namespace", "opaque", "open", "private", "protected", "section", "structure", "theorem",
      "then", "universe", "variable", "where", "with", "Prop", "Sort", "Type"
    ]);
    const commands = new Set(["#check", "#eval", "#print", "#reduce", "#synth", "#guard"]);
    const symbols = /[∀∃λΠΣ→←↔↦∧∨⊢⊣:=<>+\-*/=|!?.;,()[\]{}]/;
    const ident = (char) => /[\p{L}\p{N}_'.]/u.test(char);
    const span = (className, text) => `<span class="${className}">${escapeHtml(text)}</span>`;
    let html = "", index = 0;
    while (index < source.length) {
      const rest = source.slice(index), char = source[index];
      if (rest.startsWith("--")) {
        const end = source.indexOf("\n", index);
        const next = end < 0 ? source.length : end;
        html += span("lean-comment", source.slice(index, next)); index = next; continue;
      }
      if (rest.startsWith("/-")) {
        let depth = 0, cursor = index;
        while (cursor < source.length) {
          if (source.startsWith("/-", cursor)) { depth += 1; cursor += 2; continue; }
          if (source.startsWith("-/", cursor)) { depth -= 1; cursor += 2; if (!depth) break; continue; }
          cursor += 1;
        }
        html += span("lean-comment", source.slice(index, cursor)); index = cursor; continue;
      }
      if (char === '"') {
        let cursor = index + 1;
        while (cursor < source.length) {
          if (source[cursor] === "\\") { cursor += 2; continue; }
          if (source[cursor] === '"') { cursor += 1; break; }
          cursor += 1;
        }
        html += span("lean-string", source.slice(index, cursor)); index = cursor; continue;
      }
      if (rest.startsWith("@[")) {
        const end = source.indexOf("]", index + 2), next = end < 0 ? source.length : end + 1;
        html += span("lean-attribute", source.slice(index, next)); index = next; continue;
      }
      if (char === "#" || /[\p{L}_]/u.test(char)) {
        let cursor = index + 1;
        while (cursor < source.length && ident(source[cursor])) cursor += 1;
        const token = source.slice(index, cursor);
        const shortToken = token.includes(".") ? token.slice(token.lastIndexOf(".") + 1) : token;
        html += commands.has(token) ? span("lean-command", token)
          : keywords.has(token) || keywords.has(shortToken) ? span("lean-keyword", token)
            : token.includes(".") ? span("lean-constant", token) : escapeHtml(token);
        index = cursor; continue;
      }
      if (/\d/.test(char)) {
        let cursor = index + 1;
        while (cursor < source.length && /[\d_]/.test(source[cursor])) cursor += 1;
        html += span("lean-number", source.slice(index, cursor)); index = cursor; continue;
      }
      if (symbols.test(char)) { html += span("lean-symbol", char); index += 1; continue; }
      html += escapeHtml(char); index += 1;
    }
    return html;
  }
  window.DFPLeanCode = { highlight: highlightLean };
}());
