// Penrose renderer using @penrose/core (ESM)
// Requires: npm install @penrose/core jsdom
import { JSDOM } from "jsdom";
import { compile, optimize, toSVG } from "@penrose/core";
import fs from "fs";

// Setup browser environment for mathjax
const dom = new JSDOM('<!DOCTYPE html><html><body></body></html>');
global.window = dom.window;
global.document = dom.window.document;

// Mock canvas for Penrose text label measurement
dom.window.HTMLCanvasElement.prototype.getContext = function(type) {
    if (type === '2d') {
        return {
            measureText: (text) => {
                const str = text || '';
                const len = str.length;
                return {
                    width: len * 6,
                    actualBoundingBoxLeft: 0,
                    actualBoundingBoxRight: len * 6,
                    actualBoundingBoxAscent: 9,
                    actualBoundingBoxDescent: 3,
                    fontBoundingBoxAscent: 9,
                    fontBoundingBoxDescent: 3,
                };
            },
            fillText: () => {},
            strokeText: () => {},
            getImageData: () => ({ data: [] }),
            putImageData: () => {},
            createImageData: () => ({ data: [] }),
            setTransform: () => {},
            drawImage: () => {},
            save: () => {},
            restore: () => {},
            scale: () => {},
            rotate: () => {},
            translate: () => {},
            transform: () => {},
            beginPath: () => {},
            closePath: () => {},
            moveTo: () => {},
            lineTo: () => {},
            stroke: () => {},
            fill: () => {},
            rect: () => {},
            arc: () => {},
            ellipse: () => {},
            bezierCurveTo: () => {},
            quadraticCurveTo: () => {},
            clearRect: () => {},
            clip: () => {},
            fillRect: () => {},
            strokeRect: () => {},
            arcTo: () => {},
            globalAlpha: 1,
            globalCompositeOperation: 'source-over',
            fillStyle: '#000',
            strokeStyle: '#000',
            lineWidth: 1,
            lineCap: 'butt',
            lineJoin: 'miter',
            miterLimit: 10,
            shadowBlur: 0,
            shadowColor: 'rgba(0,0,0,0)',
            shadowOffsetX: 0,
            shadowOffsetY: 0,
            font: '12px sans-serif',
            textAlign: 'start',
            textBaseline: 'alphabetic',
        };
    }
    return null;
};

async function main() {
    const args = process.argv.slice(2);
    if (args.length < 3) {
        console.error("Usage: node penrose-render.mjs <substance.sub> <style.sty> <domain.dom> [output.svg] [variation]");
        process.exit(1);
    }

    const [subPath, stylePath, domainPath, outPath = "output.svg", variation] = args;

    const substance = fs.readFileSync(subPath, "utf-8");
    const style = fs.readFileSync(stylePath, "utf-8");
    const domain = fs.readFileSync(domainPath, "utf-8");

    const trio = { substance, style, domain };

    console.log("Compiling Penrose program...");
    const compiled = await compile(trio, variation);

    if (compiled.isErr()) {
        console.error("Compilation failed:", compiled.error);
        process.exit(1);
    }

    console.log("Optimizing layout...");
    const optimized = await optimize(compiled.value);

    if (optimized.isErr()) {
        console.error("Optimization failed:", optimized.error);
        process.exit(1);
    }

    console.log("Rendering SVG...");
    const svgEl = await toSVG(optimized.value, undefined, "geometry");
    let svg = svgEl.outerHTML;

    // Post-process: fix empty text labels (Node.js canvas mock doesn't render text content)
    svg = svg.replace(/<text([^>]*)><title>`([^`]+)`.tag<\/title><\/text>/g, (match, attrs, label) => {
        const cleanAttrs = attrs.replace(/visibility=""/g, 'visibility="visible"').replace(/width="0"/g, '').replace(/height="0"/g, '');
        return `<text${cleanAttrs}><title>\`${label}\`.tag</title>${label}</text>`;
    });

    fs.writeFileSync(outPath, svg);
    console.log("SVG written to:", outPath);
}

main().catch(e => {
    console.error(e);
    process.exit(1);
});
