import { api, LineInfo, LoadRequest } from './api.js';

export interface AppState {
  fileContent: string[];
  selectedLine: number;
  lineInfos: Map<number, LineInfo>;
  declarations: string[];
  currentTarget: string;
  dependencies: string[];
  loading: boolean;
  error: string | null;
  infixOps: Record<string, string>;
  notations: Record<string, string>;
}

export function createInitialState(): AppState {
  return {
    fileContent: [],
    selectedLine: 0,
    lineInfos: new Map(),
    declarations: [],
    currentTarget: '',
    dependencies: [],
    loading: false,
    error: null,
    infixOps: {},
    notations: {},
  };
}

export class StateManager {
  private state: AppState;
  private listeners: Set<(state: AppState) => void> = new Set();

  constructor() {
    this.state = createInitialState();
  }

  getState(): AppState {
    return this.state;
  }

  setState(updater: (state: AppState) => AppState): void {
    this.state = updater(this.state);
    this.notifyListeners();
  }

  subscribe(listener: (state: AppState) => void): () => void {
    this.listeners.add(listener);
    return () => this.listeners.delete(listener);
  }

  private notifyListeners(): void {
    for (const listener of this.listeners) {
      listener(this.state);
    }
  }

  async loadFile(target: string, deps: string[]): Promise<void> {
    this.setState(s => ({ ...s, loading: true, error: null }));

    try {
      const result = await api.loadFile({ target, dependencies: deps });

      if (!result.success) {
        this.setState(s => ({ ...s, loading: false, error: result.error || 'Failed to load file' }));
        return;
      }

      const lines = target.split('\n');
      const envResult = await api.getDeclarations();
      const infixResult = await api.getInfixOps();
      const notationsResult = await api.getNotations();

      this.setState(s => ({
        ...s,
        fileContent: lines,
        selectedLine: 0,
        lineInfos: new Map(),
        declarations: envResult.declarations || [],
        currentTarget: target,
        dependencies: deps,
        loading: false,
        infixOps: infixResult.ops || {},
        notations: notationsResult.notations || {},
      }));

      await this.refreshLineInfo(0);
    } catch (e) {
      this.setState(s => ({
        ...s,
        loading: false,
        error: e instanceof Error ? e.message : 'Unknown error',
      }));
    }
  }

  async selectLine(lineIdx: number): Promise<void> {
    this.setState(s => ({ ...s, selectedLine: lineIdx }));
    await this.refreshLineInfo(lineIdx);
  }

  private async refreshLineInfo(lineIdx: number): Promise<void> {
    try {
      const result = await api.getLineInfo(lineIdx);
      if (result.success) {
        this.setState(s => {
          const newInfos = new Map(s.lineInfos);
          newInfos.set(lineIdx, {
            line: result.line,
            info: result.info,
            goals: result.goals,
          });
          return { ...s, lineInfos: newInfos };
        });
      }
    } catch (e) {
      console.error('Failed to get line info:', e);
    }
  }

  async moveUp(): Promise<void> {
    const state = this.getState();
    if (state.selectedLine > 0) {
      await this.selectLine(state.selectedLine - 1);
    }
  }

  async moveDown(): Promise<void> {
    const state = this.getState();
    if (state.selectedLine < state.fileContent.length - 1) {
      await this.selectLine(state.selectedLine + 1);
    }
  }

  async pageUp(): Promise<void> {
    const state = this.getState();
    const pageSize = Math.max(1, Math.floor(window.innerHeight / 30));
    const newLine = Math.max(0, state.selectedLine - pageSize);
    await this.selectLine(newLine);
  }

  async pageDown(): Promise<void> {
    const state = this.getState();
    const pageSize = Math.max(1, Math.floor(window.innerHeight / 30));
    const newLine = Math.min(state.fileContent.length - 1, state.selectedLine + pageSize);
    await this.selectLine(newLine);
  }

  async goTop(): Promise<void> {
    await this.selectLine(0);
  }

  async goBottom(): Promise<void> {
    const state = this.getState();
    await this.selectLine(Math.max(0, state.fileContent.length - 1));
  }
}

export const stateManager = new StateManager();
