import { stateManager, AppState } from './state.js';
import { render } from './renderer.js';
import { api } from './api.js';

export class TuiApp {
  private container: HTMLElement | null = null;

  constructor(containerId: string) {
    this.container = document.getElementById(containerId);
    if (!this.container) {
      throw new Error(`Container element '${containerId}' not found`);
    }

    stateManager.subscribe((state: AppState) => this.onStateChange(state));
    this.setupKeyboardHandlers();
    this.setupClickHandlers();
    this.loadInitialFile();
  }

  private onStateChange(state: AppState): void {
    if (this.container) {
      this.container.innerHTML = render(state);
      this.scrollToSelectedLine();
    }
  }

  private setupKeyboardHandlers(): void {
    document.addEventListener('keydown', async (e: KeyboardEvent) => {
      switch (e.key) {
        case 'ArrowUp':
        case 'k':
          e.preventDefault();
          await stateManager.moveUp();
          break;
        case 'ArrowDown':
        case 'j':
          e.preventDefault();
          await stateManager.moveDown();
          break;
        case 'PageUp':
        case 'K':
          e.preventDefault();
          await stateManager.pageUp();
          break;
        case 'PageDown':
        case 'J':
          e.preventDefault();
          await stateManager.pageDown();
          break;
        case 'Home':
        case 'g':
          if (e.shiftKey) {
            e.preventDefault();
            await stateManager.goTop();
          }
          break;
        case 'End':
        case 'G':
          if (e.shiftKey) {
            e.preventDefault();
            await stateManager.goBottom();
          }
          break;
      }
    });
  }

  private setupClickHandlers(): void {
    document.addEventListener('click', async (e: MouseEvent) => {
      const target = e.target as HTMLElement;
      const codeLine = target.closest('.code-line');
      if (codeLine) {
        const lineIdx = parseInt(codeLine.getAttribute('data-line') || '0', 10);
        await stateManager.selectLine(lineIdx);
      }
    });
  }

  private scrollToSelectedLine(): void {
    const state = stateManager.getState();
    const selectedEl = this.container?.querySelector('.code-line.selected');
    if (selectedEl) {
      selectedEl.scrollIntoView({ behavior: 'smooth', block: 'center' });
    }
  }

  private async loadInitialFile(): Promise<void> {
    const params = new URLSearchParams(window.location.search);
    const target = params.get('target');
    const depsParam = params.get('deps');

    if (target) {
      try {
        const response = await fetch(`/api/file?path=${encodeURIComponent(target)}`);
        if (response.ok) {
          const content = await response.text();
          const deps = depsParam ? depsParam.split(',').map(d => d.trim()) : [];
          await stateManager.loadFile(content, deps);
        } else {
          console.error('Failed to load target file:', response.status);
        }
      } catch (e) {
        console.error('Error loading target file:', e);
      }
    } else {
      const demoContent = `-- Demo CIC file
-- Use ?target=<path>&deps=<dep1>,<dep2> to load a specific file

theorem demo_theorem : forall (n : Nat), Nat := by
  intro n
  exact n
`;

      const state = stateManager.getState();
      stateManager.setState(s => ({
        ...s,
        fileContent: demoContent.split('\n'),
        declarations: [],
        currentTarget: 'demo',
        loading: false,
      }));
    }
  }
}
