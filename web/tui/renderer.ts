import { AppState } from './state.js';

export function render(state: AppState): string {
  if (state.loading) {
    return `<div class="loading">Loading...</div>`;
  }

  if (state.error) {
    return `<div class="error">${escapeHtml(state.error)}</div>`;
  }

  return `
    <div class="app">
      <div class="main-content">
        ${renderCodePanel(state)}
        ${renderInfoPanel(state)}
      </div>
      ${renderStatusBar(state)}
    </div>
  `;
}

function renderCodePanel(state: AppState): string {
  const lines = state.fileContent.length > 0 ? state.fileContent : [''];
  const visibleStart = Math.max(0, state.selectedLine - 20);
  const visibleEnd = Math.min(lines.length, state.selectedLine + 30);

  let codeLines = '';
  for (let i = visibleStart; i < visibleEnd; i++) {
    const isSelected = i === state.selectedLine;
    const lineNum = i + 1;
    const lineClass = isSelected ? 'selected' : '';
    const marker = isSelected ? '>' : ' ';
    codeLines += `<div class="code-line ${lineClass}" data-line="${i}">
      <span class="line-num">${String(lineNum).padStart(3)}</span>
      <span class="line-marker">${marker}</span>
      <span class="line-content">${escapeHtml(lines[i])}</span>
    </div>`;
  }

  return `
    <div class="code-panel">
      <div class="panel-header">Source</div>
      <div class="code-content" id="code-content">
        ${codeLines}
      </div>
    </div>
  `;
}

function renderInfoPanel(state: AppState): string {
  const lineInfo = state.lineInfos.get(state.selectedLine);
  const infoLines = lineInfo?.info || [];

  let infoContent = '';
  if (infoLines.length === 0) {
    infoContent = '<div class="info-empty">⊢ (no info)</div>';
  } else {
    infoContent = infoLines.map(line => `<div class="info-line">${escapeHtml(line)}</div>`).join('');
  }

  if (lineInfo?.goals && lineInfo.goals.length > 0) {
    infoContent += renderGoals(lineInfo.goals);
  }

  return `
    <div class="info-panel">
      <div class="panel-header">Goals / Types</div>
      <div class="info-content" id="info-content">
        ${infoContent}
      </div>
    </div>
  `;
}

function renderGoals(goals: { hypotheses: string[]; goal: string }[]): string {
  let html = '<div class="goals-section">';

  for (let i = 0; i < goals.length; i++) {
    if (i > 0) {
      html += '<div class="goal-separator"></div>';
    }

    const goal = goals[i];
    if (goal.hypotheses.length > 0) {
      html += '<div class="hypotheses">';
      for (const h of goal.hypotheses) {
        html += `<div class="hypothesis">${escapeHtml(h)}</div>`;
      }
      html += '</div>';
    }

    html += `<div class="goal">⊢ ${escapeHtml(goal.goal)}</div>`;
  }

  html += '</div>';
  return html;
}

function renderStatusBar(state: AppState): string {
  const line = state.selectedLine + 1;
  const total = state.fileContent.length;
  const declCount = state.declarations.length;

  return `
    <div class="status-bar">
      <span>Line ${line}/${total}</span>
      <span>|</span>
      <span>${declCount} declarations</span>
      ${state.currentTarget ? `<span>|</span><span>${escapeHtml(state.currentTarget)}</span>` : ''}
    </div>
  `;
}

function escapeHtml(text: string): string {
  const div = document.createElement('div');
  div.textContent = text;
  return div.innerHTML;
}
