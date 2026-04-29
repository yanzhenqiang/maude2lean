// Scan all .cic files for theorems, generate Penrose SVG for each,
// and build an index.html with a selector.
// Usage: node web/generate-all.mjs <out-dir> <cic-file>...

import fs from "fs";
import path from "path";
import { spawnSync } from "child_process";
import config from "./gallery-config.mjs";

function main() {
    const args = process.argv.slice(2);
    const outDir = args[0] || config.outDir;
    const cicFiles = args.length > 1 ? args.slice(1) : config.cicFiles;

    if (!outDir || cicFiles.length === 0) {
        console.error("Usage: node generate-all.mjs <out-dir> <cic-file>...");
        process.exit(1);
    }

    fs.mkdirSync(outDir, { recursive: true });

    // Collect geometry-related theorems from all files
    const geoKeywords = ['Point', 'Line', 'on_line', 'between', 'collinear',
        'parallel', 'perpendicular', 'triangle', 'isosceles', 'equilateral',
        'midpoint', 'seg_congruent', 'angle_congruent', 'right_angle', 'on_circle'];

    const theorems = [];
    for (const file of cicFiles) {
        const content = fs.readFileSync(file, "utf-8");
        const lines = content.split("\n");
        for (let i = 0; i < lines.length; i++) {
            const line = lines[i].trim();
            const m = line.match(/^theorem\s+(\w+)\s*:/);
            if (m) {
                const name = m[1];
                // Collect full declaration (stop at := or next theorem)
                let decl = line;
                for (let j = i + 1; j < lines.length; j++) {
                    const next = lines[j];
                    if (next.match(/^theorem\s+/)) {
                        break;
                    }
                    if (next.includes(":=")) {
                        decl += "\n" + next.split(":=")[0].trim();
                        break;
                    }
                    decl += "\n" + next.trim();
                }
                // Only keep geometry-related theorems
                const isGeo = geoKeywords.some(kw => decl.includes(kw));
                if (isGeo) {
                    theorems.push({ name, decl, file });
                }
            }
        }
    }

    console.log(`Found ${theorems.length} theorems`);

    // Generate Penrose files for each theorem
    const results = [];
    for (const th of theorems) {
        const thDir = path.join(outDir, th.name);
        fs.mkdirSync(thDir, { recursive: true });

        // Generate trio
        const gen = spawnSync("node", [
            "web/cic-to-penrose.mjs",
            th.name,
            thDir,
            ...cicFiles,
        ], { encoding: "utf-8", cwd: process.cwd() });

        if (gen.status !== 0) {
            console.error(`  SKIP ${th.name}: ${gen.stderr}`);
            continue;
        }

        // Render SVG with random variation for diverse layouts
        const render = spawnSync("node", [
            "web/penrose-render.mjs",
            path.join(thDir, "geometry.substance"),
            path.join(thDir, "geometry.style"),
            path.join(thDir, "geometry.domain"),
            path.join(thDir, "output.svg"),
            th.name + "-" + Date.now(),
        ], { encoding: "utf-8", cwd: process.cwd() });

        if (render.status !== 0) {
            console.error(`  RENDER FAIL ${th.name}: ${render.stderr}`);
            continue;
        }

        // Read substance for the panel
        const substance = fs.readFileSync(path.join(thDir, "geometry.substance"), "utf-8");

        results.push({
            name: th.name,
            decl: th.decl,
            substance,
            svgPath: `./${th.name}/output.svg`,
        });
        console.log(`  OK ${th.name}`);
    }

    // Build index.html
    const indexHtml = buildIndex(results);
    fs.writeFileSync(path.join(outDir, "index.html"), indexHtml);
    console.log(`\nGenerated ${path.join(outDir, "index.html")}`);
}

function buildIndex(theorems) {
    const options = theorems
        .map((t) => {
            const sel = t.name === "butterfly" ? " selected" : "";
            return `    <option value="${t.name}"${sel}>${t.name}</option>`;
        })
        .join("\n");

    const data = JSON.stringify(
        theorems.map((t) => ({
            name: t.name,
            decl: t.decl,
            substance: t.substance,
            svgPath: t.svgPath,
        }))
    );

    return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <title>CIC Geometry Theorem Viewer</title>
    <style>
        body { font-family: system-ui, -apple-system, sans-serif; margin: 0; padding: 20px; background: #f5f5f5; }
        h1 { text-align: center; margin-bottom: 10px; }
        .selector { text-align: center; margin-bottom: 20px; }
        select { font-size: 16px; padding: 8px 16px; border-radius: 4px; }
        button { font-size: 14px; padding: 8px 16px; border-radius: 4px; cursor: pointer; margin-left: 8px; }
        #recompileBtn { background: #333; color: white; border: none; }
        #recompileBtn:disabled { background: #999; }
        .container { max-width: 900px; margin: 0 auto; }
        .panel { background: white; border-radius: 8px; box-shadow: 0 2px 4px rgba(0,0,0,0.1); margin-bottom: 20px; overflow: hidden; }
        .panel-header { background: #333; color: white; padding: 10px 16px; font-weight: bold; font-size: 14px; }
        .panel-body { padding: 16px; }
        pre { margin: 0; font-family: "SF Mono", Monaco, monospace; font-size: 12px; line-height: 1.5; overflow-x: auto; white-space: pre-wrap; }
        code { color: #333; }
        .svg-container { display: flex; justify-content: center; align-items: center; min-height: 300px; }
        .svg-container img { max-width: 100%; height: auto; }
        .hidden { display: none; }
        .status { text-align: center; color: #666; font-size: 14px; margin-top: 8px; min-height: 20px; }
    </style>
</head>
<body>
    <h1>CIC Geometry → Penrose Diagram</h1>
    <div class="selector">
        <select id="theoremSelect">
${options}
        </select>
        <button id="resampleBtn">Resample</button>
        <button id="recompileBtn">Resample All</button>
    </div>
    <div id="status" class="status"></div>
    <div id="content" class="container">
        <div class="panel">
            <div class="panel-header">CIC Declaration</div>
            <div class="panel-body"><pre><code id="cicCode"></code></pre></div>
        </div>
        <div class="panel">
            <div class="panel-header">Penrose Substance (Auto-generated)</div>
            <div class="panel-body"><pre><code id="substanceCode"></code></pre></div>
        </div>
        <div class="panel">
            <div class="panel-header">Penrose Rendering</div>
            <div class="panel-body svg-container"><img id="svgImg" src="" alt="Penrose diagram"></div>
        </div>
    </div>
    <script>
        const THEOREMS = ${data};
        const select = document.getElementById('theoremSelect');
        const content = document.getElementById('content');
        const cicCode = document.getElementById('cicCode');
        const substanceCode = document.getElementById('substanceCode');
        const svgImg = document.getElementById('svgImg');
        const resampleBtn = document.getElementById('resampleBtn');
        const recompileBtn = document.getElementById('recompileBtn');
        const statusEl = document.getElementById('status');

        function loadTheorem(name, bustCache) {
            const t = THEOREMS.find(x => x.name === name);
            if (!t) return;
            cicCode.textContent = t.decl;
            substanceCode.textContent = t.substance;
            svgImg.src = t.svgPath + (bustCache ? '?t=' + Date.now() : '');
            content.classList.remove('hidden');
        }

        select.addEventListener('change', () => loadTheorem(select.value, true));

        resampleBtn.addEventListener('click', async () => {
            const name = select.value;
            if (!name) return;
            resampleBtn.disabled = true;
            statusEl.textContent = 'Resampling ' + name + '...';
            try {
                const res = await fetch('/api/resample', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ theorem: name, variation: Date.now().toString() }),
                });
                const text = await res.text();
                if (res.ok) {
                    statusEl.textContent = 'Resample done.';
                    loadTheorem(name, true);
                    setTimeout(() => { statusEl.textContent = ''; }, 2000);
                } else {
                    statusEl.textContent = 'Resample failed: ' + text;
                }
            } catch (e) {
                statusEl.textContent = 'Error: ' + e.message;
            } finally {
                resampleBtn.disabled = false;
            }
        });

        recompileBtn.addEventListener('click', async () => {
            recompileBtn.disabled = true;
            statusEl.textContent = 'Resampling all theorems...';
            try {
                const res = await fetch('/api/recompile', { method: 'POST' });
                const text = await res.text();
                if (res.ok) {
                    statusEl.textContent = 'Recompile done. Refreshing...';
                    loadTheorem(select.value, true);
                    setTimeout(() => { statusEl.textContent = ''; }, 2000);
                } else {
                    statusEl.textContent = 'Recompile failed: ' + text;
                }
            } catch (e) {
                statusEl.textContent = 'Error: ' + e.message;
            } finally {
                recompileBtn.disabled = false;
            }
        });

        loadTheorem('butterfly', true);
    </script>
</body>
</html>
`;
}

main();
