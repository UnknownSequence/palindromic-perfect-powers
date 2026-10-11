// Minimal stand-in for poppler's `pdftotext`, built on PDFKit (macOS).
//
// It supports exactly the two invocations used by build.py:
//
//   pdftotext -f P -l P file.pdf -     print the text of page P to stdout
//   pdftotext file.pdf out.txt         write the text of all pages to out.txt
//
// As with poppler, every page is followed by a form feed. The ligature characters
// U+FB00-U+FB04 (ff, fi, fl, ffi, ffl) are expanded into their letters, so that a ligature
// counts as the letters it shows. Character counts can differ from poppler's by a few
// characters (PDFKit and poppler order and separate glyphs slightly differently).
//
// Build: swiftc -O -o pdftotext pdftotext.swift
import Foundation
import PDFKit

func fail(_ msg: String) -> Never {
    FileHandle.standardError.write(("pdftotext (PDFKit): " + msg + "\n").data(using: .utf8)!)
    exit(1)
}

let ligatures: [Character: String] = [
    "\u{FB00}": "ff", "\u{FB01}": "fi", "\u{FB02}": "fl", "\u{FB03}": "ffi", "\u{FB04}": "ffl",
]

func pageText(_ doc: PDFDocument, _ index: Int) -> String {
    guard let page = doc.page(at: index) else { fail("no page \(index + 1)") }
    var out = ""
    for ch in page.string ?? "" {
        if let rep = ligatures[ch] { out += rep } else { out.append(ch) }
    }
    return out + "\n\u{0C}"
}

var args = Array(CommandLine.arguments.dropFirst())
var first: Int? = nil
var last: Int? = nil
var positional: [String] = []
var i = 0
while i < args.count {
    let a = args[i]
    if a == "-f" || a == "-l" {
        guard i + 1 < args.count, let v = Int(args[i + 1]), v >= 1 else { fail("bad value for \(a)") }
        if a == "-f" { first = v } else { last = v }
        i += 2
    } else if a.hasPrefix("-") && a != "-" {
        fail("unsupported option \(a)")
    } else {
        positional.append(a)
        i += 1
    }
}
guard positional.count == 2 else { fail("usage: pdftotext [-f P -l P] file.pdf (out.txt | -)") }
let input = positional[0], output = positional[1]
guard let doc = PDFDocument(url: URL(fileURLWithPath: input)) else { fail("cannot open \(input)") }
let n = doc.pageCount
let lo = max(1, first ?? 1), hi = min(n, last ?? n)
var text = ""
if lo <= hi {
    for p in lo...hi { text += pageText(doc, p - 1) }
}
if output == "-" {
    FileHandle.standardOutput.write(text.data(using: .utf8)!)
} else {
    do { try text.write(toFile: output, atomically: true, encoding: .utf8) } catch { fail("cannot write \(output)") }
}
