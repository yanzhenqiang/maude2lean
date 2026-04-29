// Parse .cic geometry declarations and generate Penrose trio files dynamically.
// Usage: node cic-to-penrose.mjs <theorem-name> <out-dir> <cic-file>...

import fs from "fs";
import path from "path";

const GEO_PREDICATES = {
    "on_line":       { penrose: "OnLine",       args: ["Point", "Line"] },
    "between":       { penrose: "Between",      args: ["Point", "Point", "Point"] },
    "seg_congruent": { penrose: "SegCongruent", args: ["Point", "Point", "Point", "Point"] },
    "angle_congruent": { penrose: "AngleCongruent", args: ["Point", "Point", "Point", "Point", "Point", "Point"] },
    "parallel":      { penrose: "Parallel",     args: ["Line", "Line"] },
    "perpendicular": { penrose: "Perpendicular", args: ["Line", "Line"] },
    "collinear":     { penrose: "Collinear",    args: ["Point", "Point", "Point"] },
    "midpoint":      { penrose: "Midpoint",     args: ["Point", "Point", "Point"] },
    "right_angle":   { penrose: "RightAngle",   args: ["Point", "Point", "Point"] },
    "triangle":      { penrose: "Triangle",     args: ["Point", "Point", "Point"] },
    "on_circle":     { penrose: "OnCircle",     args: ["Point", "Point", "Point"] },
    "isosceles":     { penrose: "Isosceles",    args: ["Point", "Point", "Point"] },
    "equilateral":   { penrose: "Equilateral",  args: ["Point", "Point", "Point"] },
    "rectangle":     { penrose: "Rectangle",    args: ["Point", "Point", "Point", "Point"] },
    "parallelogram": { penrose: "Parallelogram", args: ["Point", "Point", "Point", "Point"] },
};

// Visual layout constants for Penrose Style generation
const LAYOUT = {
    pointRadius: 3.0,
    pointLabelOffset: 8.0,
    lineStrokeWidth: 1.5,
    segStrokeWidth: 1.0,
    circleStrokeWidth: 1.0,
    minPointSeparation: 15.0,
    minEndpointSeparation: 10.0,
    minMidpointSeparation: 10.0,
    minChordSeparation: 20.0,
    triangleVertexSep: 15.0,
    rectVertexSep: 15.0,
    parallelMinDist: 20.0,
};

function main() {
    const args = process.argv.slice(2);
    if (args.length < 3) {
        console.error("Usage: node cic-to-penrose.mjs <theorem-name> <out-dir> <cic-file>...");
        process.exit(1);
    }

    const theoremName = args[0];
    const outDir = args[1];
    const cicFiles = args.slice(2);

    // Scan all CIC files to discover which predicates are actually used
    let usedPredicates = new Set();
    for (const file of cicFiles) {
        const content = fs.readFileSync(file, "utf-8");
        for (const name of Object.keys(GEO_PREDICATES)) {
            if (content.includes(name)) {
                usedPredicates.add(name);
            }
        }
    }

    // Find target theorem
    let theorem = null;
    for (const file of cicFiles) {
        const content = fs.readFileSync(file, "utf-8");
        theorem = findTheorem(content, theoremName);
        if (theorem) break;
    }

    if (!theorem) {
        console.error(`Theorem '${theoremName}' not found.`);
        process.exit(1);
    }

    // Generate Penrose files dynamically
    fs.mkdirSync(outDir, { recursive: true });

    const domain = generateDomain(usedPredicates);
    const style = generateStyle(usedPredicates);
    const substance = theoremToSubstance(theorem);

    fs.writeFileSync(path.join(outDir, "geometry.domain"), domain);
    fs.writeFileSync(path.join(outDir, "geometry.substance"), substance);
    fs.writeFileSync(path.join(outDir, "geometry.style"), style);

    console.log("Generated Penrose files:");
    console.log("  Domain:   ", path.join(outDir, "geometry.domain"));
    console.log("  Substance:", path.join(outDir, "geometry.substance"));
    console.log("  Style:    ", path.join(outDir, "geometry.style"));
}

// ---------------------------------------------------------------------------
// CIC Parsing
// ---------------------------------------------------------------------------

function findTheorem(content, name) {
    const lines = content.split("\n");
    for (let i = 0; i < lines.length; i++) {
        const line = lines[i].trim();
        const prefix = `theorem ${name} :`;
        if (line.startsWith(prefix)) {
            let decl = line.slice(prefix.length).trim();
            for (let j = i + 1; j < lines.length; j++) {
                const nextLine = lines[j];
                if (nextLine.includes(":=")) {
                    decl += " " + nextLine.split(":=")[0].trim();
                    break;
                }
                decl += " " + nextLine.trim();
            }
            return { kind: "theorem", name, type: decl };
        }
    }
    return null;
}

function parsePiType(typeStr) {
    const params = [];
    let rest = typeStr.trim();

    // Remove leading forall
    const forallRegex = /^forall\s+/;
    if (forallRegex.test(rest)) {
        rest = rest.replace(forallRegex, "").trim();
    }

    // Parse binders like (A B C : Point), (h : isosceles A B C)
    while (true) {
        // Strip leading forall before each binder
        if (/^forall\s+/.test(rest)) {
            rest = rest.replace(/^forall\s+/, "").trim();
        }
        const binderMatch = rest.match(/^\(([^)]+)\)\s*,?\s*/);
        if (!binderMatch) break;

        const binderContent = binderMatch[1].trim();
        rest = rest.slice(binderMatch[0].length).trim();

        const colonIdx = binderContent.lastIndexOf(":");
        if (colonIdx === -1) continue;

        const names = binderContent.slice(0, colonIdx).trim().split(/\s+/);
        const ty = binderContent.slice(colonIdx + 1).trim();

        for (const name of names) {
            params.push({ name: name.trim(), type: ty });
        }
    }

    // Split remaining type by '->' to separate hypotheses from conclusion
    const arrowParts = splitByArrow(rest);
    const conclusion = arrowParts.pop().trim();

    for (const hyp of arrowParts) {
        const trimmed = hyp.trim();
        if (trimmed) {
            params.push({ name: `_hyp${params.length}`, type: trimmed });
        }
    }

    return { params, conclusion };
}

function splitByArrow(str) {
    const parts = [];
    let depth = 0;
    let current = "";
    for (let i = 0; i < str.length; i++) {
        const c = str[i];
        if (c === "(") depth++;
        if (c === ")") depth--;
        if (c === "-" && str[i + 1] === ">" && depth === 0) {
            parts.push(current.trim());
            current = "";
            i++;
        } else {
            current += c;
        }
    }
    parts.push(current.trim());
    return parts;
}

// ---------------------------------------------------------------------------
// Substance Generation
// ---------------------------------------------------------------------------

function theoremToSubstance(theorem) {
    const type = theorem.type;
    const { params, conclusion } = parsePiType(type);
    const n = params.length;

    const bvarName = (k) => {
        const idx = Math.max(0, n - 1 - k);
        if (idx < n) {
            return cleanName(params[idx].name);
        }
        return `v${k}`;
    };

    let out = `-- Theorem: ${theorem.name}\n`;

    const declared = new Set();
    for (const p of params) {
        const short = cleanName(p.name);
        if (isPointName(short) && !declared.has(short)) {
            out += `Point ${short}\n`;
            declared.add(short);
        }
        if (isLineType(p.type) && !declared.has(short)) {
            out += `Line ${short}\n`;
            declared.add(short);
        }
    }

    let hasHyp = false;
    for (let i = 0; i < n; i++) {
        const pred = exprToPredicate(params[i].type, i, bvarName);
        if (pred) {
            if (!hasHyp) {
                out += "\n-- Given:\n";
                hasHyp = true;
            }
            out += pred;
        }
    }

    const conclPred = exprToPredicate(conclusion, n, bvarName, true);
    if (conclPred) {
        out += "\n-- Prove:\n";
        out += conclPred;
    }

    return out;
}

function exprToPredicate(exprStr, baseDepth, bvarName, isGoal = false) {
    // Strip leading Not( ... )
    let str = exprStr.trim();
    const notMatch = str.match(/^Not\s*\((.*)\)$/);
    if (notMatch) {
        str = notMatch[1].trim();
    }

    const match = str.match(/^(\w+)\s+(.+)$/);
    if (!match) return null;

    const pred = match[1];
    const argsStr = match[2];

    if (!GEO_PREDICATES[pred]) return null;

    const args = parseArgs(argsStr);
    if (args.length === 0) return null;

    const argNames = args.map(a => argToName(a, baseDepth, bvarName));
    const name = (isGoal ? "Goal_" : "") + GEO_PREDICATES[pred].penrose;
    return `${name}(${argNames.join(", ")})\n`;
}

function parseArgs(str) {
    const args = [];
    let depth = 0;
    let current = "";
    for (const c of str) {
        if (c === "(") depth++;
        if (c === ")") depth--;
        if (c === " " && depth === 0) {
            if (current.trim()) args.push(current.trim());
            current = "";
        } else {
            current += c;
        }
    }
    if (current.trim()) args.push(current.trim());
    return args;
}

function argToName(argStr, baseDepth, bvarName) {
    const bvarMatch = argStr.match(/^BVar\((\d+)\)$/);
    if (bvarMatch) {
        return bvarName(parseInt(bvarMatch[1]));
    }
    if (/^[A-Z][a-zA-Z0-9_]*$/.test(argStr)) {
        return argStr;
    }
    return cleanName(argStr);
}

function cleanName(name) {
    return name.split(".")[0];
}

function isPointName(name) {
    return name.length === 1 && name[0] >= "A" && name[0] <= "Z";
}

function isLineType(type) {
    return type === "Line";
}

// ---------------------------------------------------------------------------
// Domain Generation
// ---------------------------------------------------------------------------

function generateDomain(predicates) {
    let out = `-- Penrose Domain for Euclidean Geometry\n`;
    out += `-- Auto-generated from CIC geometry declarations\n\n`;
    out += `type Point\n`;
    out += `type Line\n\n`;

    for (const name of Object.keys(GEO_PREDICATES)) {
        if (predicates.has(name)) {
            const info = GEO_PREDICATES[name];
            out += `predicate ${info.penrose}(${info.args.join(", ")})\n`;
            out += `predicate Goal_${info.penrose}(${info.args.join(", ")})\n`;
        }
    }

    out += `\nfunction MakeLine(Point, Point) -> Line\n`;
    return out;
}

// ---------------------------------------------------------------------------
// Style Generation
// ---------------------------------------------------------------------------

function generateStyle(predicates) {
    let out = `-- Penrose Style for Euclidean Geometry\n`;
    out += `-- Auto-generated from CIC geometry declarations\n\n`;

    // Helper: derive Goal version of a rule (no hard constraints)
    const goal = (rule, name) =>
        rule.replace(`where ${name}(`, `where Goal_${name}(`)
            .split('\n')
            .filter(l => !l.trim().startsWith('ensure') && !l.trim().startsWith('override'))
            .join('\n');

    out += `canvas {\n`;
    out += `    width = 400\n`;
    out += `    height = 400\n`;
    out += `}\n\n`;

    // Point shape + label
    out += `forall Point p {\n`;
    out += `    p.x = ?\n`;
    out += `    p.y = ?\n`;
    out += `    p.icon = Circle {\n`;
    out += `        center: (p.x, p.y)\n`;
    out += `        r: ${LAYOUT.pointRadius}\n`;
    out += `        fillColor: rgba(0, 0, 0, 1.0)\n`;
    out += `        strokeWidth: 0.0\n`;
    out += `    }\n`;
    out += `    p.tag = Text {\n`;
    out += `        string: p.label\n`;
    out += `        center: (p.x + ${LAYOUT.pointLabelOffset}, p.y - ${LAYOUT.pointLabelOffset})\n`;
    out += `    }\n`;
    out += `}\n\n`;

    // Line shape
    out += `forall Line l {\n`;
    out += `    l.icon = Line {\n`;
    out += `        start: (?, ?)\n`;
    out += `        end: (?, ?)\n`;
    out += `        strokeColor: rgba(0, 0, 0, 1.0)\n`;
    out += `        strokeWidth: ${LAYOUT.lineStrokeWidth}\n`;
    out += `    }\n`;
    out += `}\n\n`;

    const addRule = (original, penroseName) => {
        out += original;
        out += goal(original, penroseName);
    };

    if (predicates.has("on_line")) {
        addRule(`forall Point p; Line l where OnLine(p, l) {
    ensure near(p.icon.center, l.icon.start)
    ensure near(p.icon.center, l.icon.end)
}\n\n`, "OnLine");
    }

    if (predicates.has("between")) {
        addRule(`forall Point a; Point b; Point c where Between(a, b, c) {
    seg = Line {
        start: a.icon.center
        end: c.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    ensure equal((a.x - b.x) * (a.y - c.y), (a.x - c.x) * (a.y - b.y))
    ensure greaterThan((a.x - c.x) * (a.x - c.x) + (a.y - c.y) * (a.y - c.y), 100.0)
    ensure disjoint(a.icon, b.icon, ${LAYOUT.minMidpointSeparation})
    ensure disjoint(b.icon, c.icon, ${LAYOUT.minMidpointSeparation})
}\n\n`, "Between");
    }

    if (predicates.has("midpoint")) {
        addRule(`forall Point m; Point a; Point b where Midpoint(m, a, b) {
    seg = Line {
        start: a.icon.center
        end: b.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    override m.x = (a.x + b.x) / 2.0
    override m.y = (a.y + b.y) / 2.0
    ensure disjoint(a.icon, b.icon, ${LAYOUT.minMidpointSeparation})
}\n\n`, "Midpoint");
    }

    if (predicates.has("parallel")) {
        addRule(`forall Line l; Line m where Parallel(l, m) {
    ensure disjoint(l.icon, m.icon, ${LAYOUT.parallelMinDist})
}\n\n`, "Parallel");
    }

    if (predicates.has("perpendicular")) {
        addRule(`forall Line l; Line m where Perpendicular(l, m) {
    ensure equal(l.icon.start[0], m.icon.start[0])
    ensure equal(l.icon.end[1], m.icon.end[1])
}\n\n`, "Perpendicular");
    }

    if (predicates.has("triangle")) {
        addRule(`forall Point a; Point b; Point c where Triangle(a, b, c) {
    ab = Line {
        start: a.icon.center
        end: b.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    bc = Line {
        start: b.icon.center
        end: c.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    ca = Line {
        start: c.icon.center
        end: a.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    ensure disjoint(a.icon, b.icon, ${LAYOUT.triangleVertexSep})
    ensure disjoint(b.icon, c.icon, ${LAYOUT.triangleVertexSep})
    ensure disjoint(c.icon, a.icon, ${LAYOUT.triangleVertexSep})
}\n\n`, "Triangle");
    }

    if (predicates.has("isosceles")) {
        addRule(`forall Point a; Point b; Point c where Isosceles(a, b, c) {
    ab = Line {
        start: a.icon.center
        end: b.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    bc = Line {
        start: b.icon.center
        end: c.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    ca = Line {
        start: c.icon.center
        end: a.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    ensure equal((a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y), (a.x - c.x) * (a.x - c.x) + (a.y - c.y) * (a.y - c.y))
    ensure disjoint(a.icon, b.icon, ${LAYOUT.triangleVertexSep})
    ensure disjoint(a.icon, c.icon, ${LAYOUT.triangleVertexSep})
    ensure disjoint(b.icon, c.icon, ${LAYOUT.triangleVertexSep})
}\n\n`, "Isosceles");
    }

    if (predicates.has("equilateral")) {
        addRule(`forall Point a; Point b; Point c where Equilateral(a, b, c) {
    ab = Line {
        start: a.icon.center
        end: b.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    bc = Line {
        start: b.icon.center
        end: c.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    ca = Line {
        start: c.icon.center
        end: a.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    ensure equal((a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y), (b.x - c.x) * (b.x - c.x) + (b.y - c.y) * (b.y - c.y))
    ensure equal((b.x - c.x) * (b.x - c.x) + (b.y - c.y) * (b.y - c.y), (c.x - a.x) * (c.x - a.x) + (c.y - a.y) * (c.y - a.y))
    ensure disjoint(a.icon, b.icon, ${LAYOUT.triangleVertexSep})
    ensure disjoint(b.icon, c.icon, ${LAYOUT.triangleVertexSep})
    ensure disjoint(c.icon, a.icon, ${LAYOUT.triangleVertexSep})
}\n\n`, "Equilateral");
    }

    if (predicates.has("collinear")) {
        addRule(`forall Point a; Point b; Point c where Collinear(a, b, c) {
    seg = Line {
        start: (b.x, b.y)
        end: (c.x, c.y)
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    ensure equal((a.x - b.x) * (a.y - c.y), (a.x - c.x) * (a.y - b.y))
    ensure disjoint(b.icon, c.icon, ${LAYOUT.minMidpointSeparation})
}\n\n`, "Collinear");
    }

    if (predicates.has("seg_congruent")) {
        addRule(`forall Point a; Point b; Point c; Point d where SegCongruent(a, b, c, d) {
    s1 = Line {
        start: a.icon.center
        end: b.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    s2 = Line {
        start: c.icon.center
        end: d.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    ensure equal((a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y), (c.x - d.x) * (c.x - d.x) + (c.y - d.y) * (c.y - d.y))
}\n\n`, "SegCongruent");
    }

    if (predicates.has("right_angle")) {
        addRule(`forall Point a; Point b; Point c where RightAngle(a, b, c) {
    ba = Line {
        start: b.icon.center
        end: a.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    bc = Line {
        start: b.icon.center
        end: c.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    ensure equal((a.x - b.x) * (c.x - b.x) + (a.y - b.y) * (c.y - b.y), 0.0)
}\n\n`, "RightAngle");
    }

    if (predicates.has("rectangle")) {
        addRule(`forall Point a; Point b; Point c; Point d where Rectangle(a, b, c, d) {
    ab = Line {
        start: a.icon.center
        end: b.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    bc = Line {
        start: b.icon.center
        end: c.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    cd = Line {
        start: c.icon.center
        end: d.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    da = Line {
        start: d.icon.center
        end: a.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    ensure disjoint(a.icon, b.icon, ${LAYOUT.rectVertexSep})
    ensure disjoint(b.icon, c.icon, ${LAYOUT.rectVertexSep})
    ensure disjoint(c.icon, d.icon, ${LAYOUT.rectVertexSep})
    ensure disjoint(d.icon, a.icon, ${LAYOUT.rectVertexSep})
}\n\n`, "Rectangle");
    }

    if (predicates.has("parallelogram")) {
        addRule(`forall Point a; Point b; Point c; Point d where Parallelogram(a, b, c, d) {
    ab = Line {
        start: a.icon.center
        end: b.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    bc = Line {
        start: b.icon.center
        end: c.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    cd = Line {
        start: c.icon.center
        end: d.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    da = Line {
        start: d.icon.center
        end: a.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: ${LAYOUT.segStrokeWidth}
    }
    ensure disjoint(a.icon, b.icon, ${LAYOUT.rectVertexSep})
    ensure disjoint(b.icon, c.icon, ${LAYOUT.rectVertexSep})
    ensure disjoint(c.icon, d.icon, ${LAYOUT.rectVertexSep})
    ensure disjoint(d.icon, a.icon, ${LAYOUT.rectVertexSep})
}\n\n`, "Parallelogram");
    }

    if (predicates.has("on_circle")) {
        addRule(`forall Point o; Point r; Point p where OnCircle(p, o, r) {
    o.circ = Circle {
        center: o.icon.center
        r: ?
        fillColor: rgba(0, 0, 0, 0.0)
        strokeColor: rgba(0.3, 0.3, 0.3, 1.0)
        strokeWidth: ${LAYOUT.circleStrokeWidth}
    }
    ensure equal(o.circ.r * o.circ.r, (r.x - o.x) * (r.x - o.x) + (r.y - o.y) * (r.y - o.y))
    ensure equal((p.x - o.x) * (p.x - o.x) + (p.y - o.y) * (p.y - o.y), o.circ.r * o.circ.r)
    ensure greaterThan(o.circ.r, 50.0)
}\n\n`, "OnCircle");
    }

    return out;
}

main();
