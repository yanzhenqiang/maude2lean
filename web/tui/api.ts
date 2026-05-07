const API_BASE = '/api';

export interface LoadRequest {
  target: string;
  dependencies: string[];
}

export interface TacticGoal {
  hypotheses: string[];
  goal: string;
}

export interface LineInfo {
  line: number;
  info: string[];
  goals?: TacticGoal[];
  error?: string;
}

export interface ParseResponse {
  success: boolean;
  error?: string;
}

export interface LineInfoResponse {
  success: boolean;
  line: number;
  info: string[];
  goals?: TacticGoal[];
  error?: string;
}

export interface EnvResponse {
  success: boolean;
  declarations: string[];
  error?: string;
}

class ApiClient {
  private baseUrl: string;

  constructor(baseUrl: string = API_BASE) {
    this.baseUrl = baseUrl;
  }

  async loadFile(req: LoadRequest): Promise<ParseResponse> {
    const res = await fetch(`${this.baseUrl}/load`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(req),
    });
    return res.json();
  }

  async getLineInfo(line: number): Promise<LineInfoResponse> {
    const res = await fetch(`${this.baseUrl}/line-info?line=${line}`);
    return res.json();
  }

  async getDeclarations(): Promise<EnvResponse> {
    const res = await fetch(`${this.baseUrl}/env`);
    return res.json();
  }

  async executeTactic(tactic: string): Promise<{ success: boolean; error?: string }> {
    const res = await fetch(`${this.baseUrl}/tactic`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ tactic }),
    });
    return res.json();
  }

  async getInfixOps(): Promise<{ success: boolean; ops: Record<string, string> }> {
    const res = await fetch(`${this.baseUrl}/infix-ops`);
    return res.json();
  }

  async getNotations(): Promise<{ success: boolean; notations: Record<string, string> }> {
    const res = await fetch(`${this.baseUrl}/notations`);
    return res.json();
  }
}

export const api = new ApiClient();
