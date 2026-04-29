// Debug butterfly theorem step-by-step
// Each step only declares needed points and applies needed constraints.
// Previous points are FIXED via override (their constraints are removed since
// their geometry is already encoded in their fixed coordinates).

import fs from "fs";
import path from "path";
import { spawnSync } from "child_process";

const OUT_DIR = "gallery/butterfly/debug";
fs.mkdirSync(OUT_DIR, { recursive: true });

const DOMAIN = fs.readFileSync("gallery/butterfly/geometry.domain", "utf-8");

const BASE_STYLE = `canvas {
    width = 400
    height = 400
}

forall Point p {
    p.x = ?
    p.y = ?
    p.icon = Circle {
        center: (p.x, p.y)
        r: 3
        fillColor: rgba(0, 0, 0, 1.0)
        strokeWidth: 0.0
    }
    p.tag = Text {
        string: p.label
        center: (p.x + 8, p.y - 8)
    }
}

forall Line l {
    l.icon = Line {
        start: (?, ?)
        end: (?, ?)
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: 1.5
    }
}
`;

const RULES = {
    OnCircle: `forall Point o; Point r; Point p where OnCircle(p, o, r) {
    o.circ = Circle {
        center: o.icon.center
        r: ?
        fillColor: rgba(0, 0, 0, 0.0)
        strokeColor: rgba(0.3, 0.3, 0.3, 1.0)
        strokeWidth: 1
    }
    ensure equal(o.circ.r * o.circ.r, (r.x - o.x) * (r.x - o.x) + (r.y - o.y) * (r.y - o.y))
    ensure equal((p.x - o.x) * (p.x - o.x) + (p.y - o.y) * (p.y - o.y), o.circ.r * o.circ.r)
    ensure greaterThan(o.circ.r, 50.0)
}`,
    Midpoint: `forall Point m; Point a; Point b where Midpoint(m, a, b) {
    seg = Line {
        start: a.icon.center
        end: b.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: 1
    }
    override m.x = (a.x + b.x) / 2.0
    override m.y = (a.y + b.y) / 2.0
    ensure disjoint(a.icon, b.icon, 10)
}`,
    Between: `forall Point a; Point b; Point c where Between(a, b, c) {
    seg = Line {
        start: a.icon.center
        end: c.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: 1
    }
    ensure equal((a.x - b.x) * (a.y - c.y), (a.x - c.x) * (a.y - b.y))
    ensure disjoint(a.icon, b.icon, 10)
    ensure disjoint(b.icon, c.icon, 10)
}`,
    Collinear: `forall Point a; Point b; Point c where Collinear(a, b, c) {
    seg = Line {
        start: (b.x, b.y)
        end: (c.x, c.y)
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: 1
    }
    ensure equal((a.x - b.x) * (a.y - c.y), (a.x - c.x) * (a.y - b.y))
}`,
    Goal_Midpoint: `forall Point m; Point a; Point b where Goal_Midpoint(m, a, b) {
    seg = Line {
        start: a.icon.center
        end: b.icon.center
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: 1
    }
}`,
};

const STEPS = [
    {
        name: "01-PQ",
        points: ["O", "R", "P", "Q"],
        constraints: ["OnCircle(P, O, R)", "OnCircle(Q, O, R)"],
    },
    {
        name: "02-M",
        points: ["O", "R", "P", "Q", "M"],
        constraints: ["Midpoint(M, P, Q)"],
    },
    {
        name: "03-AB",
        points: ["O", "R", "P", "Q", "M", "A", "B"],
        constraints: ["OnCircle(A, O, R)", "Between(A, M, B)", "OnCircle(B, O, R)"],
    },
    {
        name: "04-CD",
        points: ["O", "R", "P", "Q", "M", "A", "B", "C", "D"],
        constraints: ["OnCircle(C, O, R)", "Between(C, M, D)", "OnCircle(D, O, R)"],
    },
    {
        name: "05-X",
        points: ["O", "R", "P", "Q", "M", "A", "B", "C", "D", "X"],
        constraints: ["Collinear(X, P, Q)", "Collinear(X, A, D)"],
    },
    {
        name: "06-Y",
        points: ["O", "R", "P", "Q", "M", "A", "B", "C", "D", "X", "Y"],
        constraints: ["Collinear(Y, P, Q)", "Collinear(Y, B, C)"],
    },
    {
        name: "07-goal",
        points: ["O", "R", "P", "Q", "M", "A", "B", "C", "D", "X", "Y"],
        constraints: ["Goal_Midpoint(M, X, Y)"],
    },
];

function generateSubstance(points, constraints) {
    let out = "";
    for (const p of points) {
        out += `Point ${p}\n`;
    }
    out += "\n-- Given:\n";
    for (const c of constraints) {
        out += c + "\n";
    }
    return out;
}

function extractCoords(svgPath) {
    const content = fs.readFileSync(svgPath, "utf-8");
    const coords = {};
    const circleRe = /<circle([^>]*)>\s*<title>`([^`]+)`\.icon<\/title>\s*<\/circle>/g;
    for (const m of content.matchAll(circleRe)) {
        const attrs = m[1];
        const name = m[2];
        const cxMatch = attrs.match(/cx="([0-9.eE+-]+)"/);
        const cyMatch = attrs.match(/cy="([0-9.eE+-]+)"/);
        if (cxMatch && cyMatch) {
            // Penrose uses center-origin coords (y-up), SVG uses top-left (y-down)
            const svgCx = parseFloat(cxMatch[1]);
            const svgCy = parseFloat(cyMatch[1]);
            coords[name] = { x: svgCx - 200.0, y: 200.0 - svgCy };
        }
    }
    return coords;
}

function generateStyle(step, fixedCoords) {
    let style = BASE_STYLE;

    // Build comprehensive fixed-coordinate block.
    // In Penrose 3.3.0, multiple `forall Point <name>` blocks overwrite
    // each other globally. The workaround is a SINGLE block whose `where`
    // clause matches the exact graph structure of the step. All fixed
    // coordinates are set via `override` inside this one block.
    const fixedInStep = Object.entries(fixedCoords).filter(([name]) =>
        step.points.includes(name)
    );
    if (fixedInStep.length > 0) {
        const pointVars = step.points.join("; Point ");
        const whereClause = step.constraints.join("; ");
        style += `\nforall Point ${pointVars}\n`;
        if (whereClause) {
            style += `where ${whereClause} {\n`;
        } else {
            style += `{\n`;
        }
        for (const [name, c] of fixedInStep) {
            style += `    override ${name}.x = ${c.x.toFixed(4)}\n`;
            style += `    override ${name}.y = ${c.y.toFixed(4)}\n`;
        }
        style += `}\n`;
    }

    // Add only the rules needed for this step's constraints
    const added = new Set();
    for (const constraint of step.constraints) {
        const pred = constraint.split("(")[0];
        if (RULES[pred] && !added.has(pred)) {
            style += "\n" + RULES[pred] + "\n";
            added.add(pred);
        }
    }

    return style;
}

let allCoords = {};

for (const step of STEPS) {
    const substance = generateSubstance(step.points, step.constraints);
    const style = generateStyle(step, allCoords);

    fs.writeFileSync(path.join(OUT_DIR, `${step.name}.substance`), substance);
    fs.writeFileSync(path.join(OUT_DIR, `${step.name}.style`), style);
    fs.writeFileSync(path.join(OUT_DIR, `${step.name}.domain`), DOMAIN);

    console.log(`\n--- ${step.name} ---`);
    console.log(`Points: ${step.points.join(", ")}`);
    console.log(`Constraints: ${step.constraints.join(", ")}`);
    console.log(`Fixed: ${Object.keys(allCoords).filter(k => step.points.includes(k)).join(", ") || "none"}`);

    const render = spawnSync("node", [
        "web/penrose-render.mjs",
        path.join(OUT_DIR, `${step.name}.substance`),
        path.join(OUT_DIR, `${step.name}.style`),
        path.join(OUT_DIR, `${step.name}.domain`),
        path.join(OUT_DIR, `${step.name}.svg`),
        "butterfly-debug",
    ], { encoding: "utf-8", cwd: process.cwd() });

    if (render.status !== 0) {
        console.error(`  RENDER FAIL: ${render.stderr}`);
        continue;
    }

    const coords = extractCoords(path.join(OUT_DIR, `${step.name}.svg`));
    // Merge new coords
    for (const [k, v] of Object.entries(coords)) {
        allCoords[k] = v;
    }
    console.log("  Result:", Object.entries(coords).map(([k, v]) => `${k}=(${v.x.toFixed(1)},${v.y.toFixed(1)})`).join(", "));
}

// Generate index.html
const html = `<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>Butterfly Debug Steps</title>
<style>
body { font-family: system-ui, sans-serif; margin: 20px; background: #f5f5f5; }
h1 { text-align: center; }
.step { background: white; border-radius: 8px; margin-bottom: 20px; padding: 16px; box-shadow: 0 2px 4px rgba(0,0,0,0.1); }
.step h2 { margin-top: 0; font-size: 16px; }
.step img { max-width: 100%; height: auto; border: 1px solid #ddd; }
.nav { text-align: center; margin-bottom: 20px; }
.nav a { display: inline-block; padding: 8px 16px; margin: 4px; background: #333; color: white; text-decoration: none; border-radius: 4px; }
.nav a:hover { background: #555; }
</style>
</head>
<body>
<h1>Butterfly Theorem — Step by Step</h1>
<div class="nav">
${STEPS.map((s, i) => `<a href="#step-${i}">${s.name}</a>`).join("\n")}
</div>
${STEPS.map((s, i) => `
<div class="step" id="step-${i}">
<h2>Step ${i + 1}: ${s.name}</h2>
<p>Points: ${s.points.join(", ")}</p>
<p>Constraints: ${s.constraints.join(", ")}</p>
<img src="${s.name}.svg" alt="${s.name}">
</div>
`).join("\n")}
</body>
</html>`;
fs.writeFileSync(path.join(OUT_DIR, "index.html"), html);

console.log("\n=== Done ===");
console.log("Open: http://localhost:8080/gallery/butterfly/debug/index.html");
