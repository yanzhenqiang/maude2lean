import http from 'http';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import { spawn } from 'child_process';
import config from './gallery-config.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(__dirname, '..');

const mime = {
  '.html': 'text/html',
  '.js': 'text/javascript',
  '.mjs': 'text/javascript',
  '.css': 'text/css',
  '.json': 'application/json',
  '.svg': 'image/svg+xml',
  '.png': 'image/png',
};

const server = http.createServer(async (req, res) => {
  const url = req.url;

  if (url === '/') {
    res.writeHead(302, { 'Location': '/gallery/index.html' });
    res.end();
    return;
  }

  if (url === '/api/recompile' && req.method === 'POST') {
    res.setHeader('Content-Type', 'text/plain; charset=utf-8');
    const outDir = path.join(root, config.outDir);
    const entries = fs.readdirSync(outDir, { withFileTypes: true });
    const dirs = entries.filter(e => e.isDirectory()).map(e => e.name);
    const results = [];

    for (const dir of dirs) {
      const thDir = path.join(outDir, dir);
      const subPath = path.join(thDir, 'geometry.substance');
      const stylePath = path.join(thDir, 'geometry.style');
      const domainPath = path.join(thDir, 'geometry.domain');
      const outPath = path.join(thDir, 'output.svg');
      if (!fs.existsSync(subPath) || !fs.existsSync(stylePath) || !fs.existsSync(domainPath)) {
        continue;
      }
      const variation = Date.now().toString() + '-' + dir;
      const child = spawn('node', [
        'web/penrose-render.mjs', subPath, stylePath, domainPath, outPath, variation,
      ], { cwd: root, stdio: ['ignore', 'pipe', 'pipe'] });

      let stderr = '';
      child.stderr.on('data', (d) => { stderr += d; });

      const code = await new Promise(resolve => child.on('close', resolve));
      results.push({ dir, ok: code === 0, stderr });
    }

    const failed = results.filter(r => !r.ok);
    if (failed.length === 0) {
      res.writeHead(200);
      res.end('Resampled ' + results.length + ' theorems');
    } else {
      res.writeHead(500);
      res.end('Failed: ' + failed.map(f => f.dir + ': ' + f.stderr).join('; '));
    }
    return;
  }

  if (url === '/api/resample' && req.method === 'POST') {
    let body = '';
    req.on('data', (d) => { body += d; });
    req.on('end', () => {
      try {
        const { theorem, variation } = JSON.parse(body);
        if (!theorem) {
          res.writeHead(400); res.end('Missing theorem'); return;
        }
        const thDir = path.join(root, config.outDir, theorem);
        const subPath = path.join(thDir, 'geometry.substance');
        const stylePath = path.join(thDir, 'geometry.style');
        const domainPath = path.join(thDir, 'geometry.domain');
        const outPath = path.join(thDir, 'output.svg');

        if (!fs.existsSync(subPath) || !fs.existsSync(stylePath) || !fs.existsSync(domainPath)) {
          res.writeHead(404); res.end('Theorem trio not found'); return;
        }

        res.setHeader('Content-Type', 'text/plain; charset=utf-8');
        const varArg = variation || Date.now().toString();
        const child = spawn('node', [
          'web/penrose-render.mjs',
          subPath, stylePath, domainPath, outPath, varArg,
        ], { cwd: root, stdio: ['ignore', 'pipe', 'pipe'] });

        let stdout = '';
        let stderr = '';
        child.stdout.on('data', (d) => { stdout += d; });
        child.stderr.on('data', (d) => { stderr += d; });

        child.on('close', (code) => {
          if (code === 0) {
            res.writeHead(200);
            res.end(stdout || 'OK');
          } else {
            res.writeHead(500);
            res.end(stderr || 'Resample failed');
          }
        });
      } catch (e) {
        res.writeHead(400);
        res.end('Invalid JSON: ' + e.message);
      }
    });
    return;
  }

  const filePath = path.join(root, decodeURIComponent(url.split('?')[0]));

  if (!filePath.startsWith(root)) {
    res.writeHead(403); res.end('Forbidden'); return;
  }

  if (!fs.existsSync(filePath) || fs.statSync(filePath).isDirectory()) {
    res.writeHead(404); res.end('Not found'); return;
  }

  const ext = path.extname(filePath);
  res.writeHead(200, { 'Content-Type': mime[ext] || 'application/octet-stream' });
  res.end(fs.readFileSync(filePath));
});

server.listen(8080, '0.0.0.0', () => {
  console.log('Server running at http://localhost:8080/');
  console.log('Gallery: http://localhost:8080/gallery/index.html');
});
