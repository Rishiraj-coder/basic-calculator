/* ==========================================================================
   AETHER CALC - CORE ENGINE & UI CONTROLLER
   ========================================================================== */

document.addEventListener('DOMContentLoaded', () => {
  // --- UI Elements ---
  const expressionScreen = document.getElementById('expression-screen');
  const inputScreen = document.getElementById('input-screen');
  const modeStdBtn = document.getElementById('mode-std');
  const modeSciBtn = document.getElementById('mode-sci');
  const scientificKeypad = document.getElementById('scientific-keypad');
  const appContainer = document.querySelector('.app-container');
  const degRadToggle = document.getElementById('deg-rad-toggle');
  const historyBtn = document.getElementById('history-btn');
  const historyDrawer = document.getElementById('history-drawer');
  const closeHistoryBtn = document.getElementById('close-history-btn');
  const historyList = document.getElementById('history-list');
  const historyEmpty = document.getElementById('history-empty');
  const clearHistoryBtn = document.getElementById('clear-history-btn');
  const toast = document.getElementById('toast');
  const accentDots = document.querySelectorAll('.accent-dot');

  // --- Calculator State ---
  let expression = '';       // The active math formula string shown in display
  let lastResult = null;      // Stores the last successful evaluation result
  let isRadians = true;       // True = Radians, False = Degrees
  let lastEvaluated = false;  // True if the display is showing an evaluation result
  let history = [];           // Array of { expression, result }

  // --- Initialization ---
  initTheme();
  initHistory();
  updateDisplay();

  // ==========================================================================
  // 1. MATHEMATICAL EXPRESSION PARSER (Safe, Robust AST Evaluator)
  // ==========================================================================

  // --- Tokenizer ---
  function tokenize(str) {
    const tokens = [];
    let i = 0;

    // Normalizing characters to standard programming operators
    let normalized = str
      .replace(/×/g, '*')
      .replace(/÷/g, '/')
      .replace(/−/g, '-') // Unicode minus to hyphen
      .replace(/π/g, 'pi');

    while (i < normalized.length) {
      const char = normalized[i];

      if (char === ' ' || char === '\t') {
        i++;
        continue;
      }

      // 1. Numbers (including decimals)
      if (/[0-9.]/.test(char)) {
        let numStr = '';
        // Capture full number
        while (i < normalized.length && /[0-9.]/.test(normalized[i])) {
          numStr += normalized[i];
          i++;
        }
        tokens.push({ type: 'NUMBER', value: numStr });
        continue;
      }

      // 2. Alphabetic Words (Functions & Constants)
      if (/[a-zA-Z]/.test(char)) {
        let word = '';
        while (i < normalized.length && /[a-zA-Z]/.test(normalized[i])) {
          word += normalized[i];
          i++;
        }

        if (word === 'sin' || word === 'cos' || word === 'tan' || word === 'log' || word === 'ln' || word === 'sqrt') {
          tokens.push({ type: 'FUNCTION', value: word });
        } else if (word === 'pi' || word === 'e') {
          tokens.push({ type: 'CONSTANT', value: word });
        } else {
          throw new Error(`Unknown identifier: ${word}`);
        }
        continue;
      }

      // 3. Parentheses & Modulo/Factorial
      if (char === '(') {
        tokens.push({ type: 'LPAREN', value: '(' });
        i++;
        continue;
      }
      if (char === ')') {
        tokens.push({ type: 'RPAREN', value: ')' });
        i++;
        continue;
      }
      if (char === '!') {
        tokens.push({ type: 'POSTFIX', value: '!' });
        i++;
        continue;
      }

      // 4. Mathematical Operators
      if (['+', '-', '*', '/', '%', '^'].includes(char)) {
        tokens.push({ type: 'OPERATOR', value: char });
        i++;
        continue;
      }

      // If we reach here, we hit an invalid character
      throw new Error(`Invalid character in expression: ${char}`);
    }

    return tokens;
  }

  // --- Implicit Multiplication Optimization ---
  // Transforms: 2pi -> 2*pi, 2(3+4) -> 2*(3+4), )2 -> )*2, )( -> )*(, etc.
  function insertImplicitMultiplication(tokens) {
    const result = [];
    for (let i = 0; i < tokens.length; i++) {
      const current = tokens[i];
      result.push(current);

      if (i < tokens.length - 1) {
        const next = tokens[i + 1];
        const currentIsOperand = ['NUMBER', 'CONSTANT', 'RPAREN', 'POSTFIX'].includes(current.type);
        const nextIsOperand = ['NUMBER', 'CONSTANT', 'LPAREN', 'FUNCTION'].includes(next.type);

        if (currentIsOperand && nextIsOperand) {
          result.push({ type: 'OPERATOR', value: '*' });
        }
      }
    }
    return result;
  }

  // --- Recursive Descent Parser ---
  class Parser {
    constructor(tokens) {
      this.tokens = tokens;
      this.pos = 0;
    }

    peek() {
      return this.tokens[this.pos] || null;
    }

    next() {
      return this.tokens[this.pos++];
    }

    parse() {
      if (this.tokens.length === 0) return null;
      const result = this.expression();
      if (this.pos < this.tokens.length) {
        throw new Error("Invalid syntax or mismatched operators");
      }
      return result;
    }

    // Expression -> Term (( '+' | '-' ) Term)*
    expression() {
      let node = this.term();
      while (true) {
        const token = this.peek();
        if (token && token.type === 'OPERATOR' && (token.value === '+' || token.value === '-')) {
          this.next();
          const right = this.term();
          node = { type: 'BINARY', op: token.value, left: node, right: right };
        } else {
          break;
        }
      }
      return node;
    }

    // Term -> Factor (( '*' | '/' | '%' ) Factor)*
    term() {
      let node = this.factor();
      while (true) {
        const token = this.peek();
        if (token && token.type === 'OPERATOR' && (token.value === '*' || token.value === '/' || token.value === '%')) {
          this.next();
          const right = this.factor();
          node = { type: 'BINARY', op: token.value, left: node, right: right };
        } else {
          break;
        }
      }
      return node;
    }

    // Factor -> Power ( '^' Power )*  (Right associative power check)
    factor() {
      let node = this.power();
      const token = this.peek();
      if (token && token.type === 'OPERATOR' && token.value === '^') {
        this.next();
        const right = this.factor(); // Recursion enforces right-associativity
        node = { type: 'BINARY', op: '^', left: node, right: right };
      }
      return node;
    }

    // Power -> Primary [ '!' ]
    power() {
      let node = this.primary();
      while (true) {
        const token = this.peek();
        if (token && token.type === 'POSTFIX' && token.value === '!') {
          this.next();
          node = { type: 'POSTFIX', op: '!', operand: node };
        } else {
          break;
        }
      }
      return node;
    }

    // Primary -> Number | Constant | ParenthesizedExpr | FunctionCall | UnaryExpr
    primary() {
      const token = this.peek();
      if (!token) {
        throw new Error("Unexpected end of expression");
      }

      // Number literal
      if (token.type === 'NUMBER') {
        this.next();
        const val = parseFloat(token.value);
        if (isNaN(val)) throw new Error(`Invalid number format: ${token.value}`);
        return { type: 'NUMBER', value: val };
      }

      // Mathematical constant
      if (token.type === 'CONSTANT') {
        this.next();
        return { type: 'CONSTANT', value: token.value };
      }

      // Unary Operator (+/-)
      if (token.type === 'OPERATOR' && (token.value === '-' || token.value === '+')) {
        this.next();
        const expr = this.primary();
        return { type: 'UNARY', op: token.value, operand: expr };
      }

      // Function Call (sin, cos, log, etc)
      if (token.type === 'FUNCTION') {
        this.next(); // Consume function token
        const openParen = this.peek();
        if (!openParen || openParen.type !== 'LPAREN') {
          throw new Error(`Missing '(' after function ${token.value}`);
        }
        this.next(); // Consume '('
        const expr = this.expression();
        const closeParen = this.next();
        if (!closeParen || closeParen.type !== 'RPAREN') {
          throw new Error(`Mismatched parenthesis in function ${token.value}`);
        }
        return { type: 'FUNCTION', name: token.value, operand: expr };
      }

      // Parenthesized expression
      if (token.type === 'LPAREN') {
        this.next(); // Consume '('
        const expr = this.expression();
        const closeParen = this.next();
        if (!closeParen || closeParen.type !== 'RPAREN') {
          throw new Error("Mismatched parenthesis: expected ')'");
        }
        return expr;
      }

      throw new Error(`Unexpected symbol: ${token.value}`);
    }
  }

  // --- AST Evaluator ---
  function evaluateAST(node) {
    if (!node) return 0;

    if (node.type === 'NUMBER') {
      return node.value;
    }

    if (node.type === 'CONSTANT') {
      if (node.value === 'pi') return Math.PI;
      if (node.value === 'e') return Math.E;
      throw new Error(`Unknown constant: ${node.value}`);
    }

    if (node.type === 'UNARY') {
      const val = evaluateAST(node.operand);
      return node.op === '-' ? -val : val;
    }

    if (node.type === 'POSTFIX') {
      if (node.op === '!') {
        const val = evaluateAST(node.operand);
        return factorial(val);
      }
      throw new Error(`Unknown postfix operator: ${node.op}`);
    }

    if (node.type === 'BINARY') {
      const left = evaluateAST(node.left);
      const right = evaluateAST(node.right);
      switch (node.op) {
        case '+': return left + right;
        case '-': return left - right;
        case '*': return left * right;
        case '/':
          if (right === 0) throw new Error("Division by zero");
          return left / right;
        case '%': return left % right;
        case '^': return Math.pow(left, right);
        default: throw new Error(`Unknown operator: ${node.op}`);
      }
    }

    if (node.type === 'FUNCTION') {
      let val = evaluateAST(node.operand);
      switch (node.name) {
        case 'sin':
          if (!isRadians) val = (val * Math.PI) / 180;
          return cleanFloat(Math.sin(val));
        case 'cos':
          if (!isRadians) val = (val * Math.PI) / 180;
          return cleanFloat(Math.cos(val));
        case 'tan':
          if (!isRadians) val = (val * Math.PI) / 180;
          // Check for undefined tangent (e.g. cos = 0)
          if (Math.abs(Math.cos(val)) < 1e-15) throw new Error("Tangent undefined");
          return cleanFloat(Math.tan(val));
        case 'log':
          if (val <= 0) throw new Error("Log base 10 input must be > 0");
          return Math.log10(val);
        case 'ln':
          if (val <= 0) throw new Error("Natural log input must be > 0");
          return Math.log(val);
        case 'sqrt':
          if (val < 0) throw new Error("Square root of negative number");
          return Math.sqrt(val);
        default:
          throw new Error(`Unknown function: ${node.name}`);
      }
    }

    throw new Error("Invalid calculation element");
  }

  // Factorial utility
  function factorial(n) {
    if (n < 0 || !Number.isInteger(n)) {
      throw new Error("Factorial requires non-negative integers");
    }
    if (n > 170) return Infinity; // Max floating point value limitation
    let result = 1;
    for (let i = 2; i <= n; i++) {
      result *= i;
    }
    return result;
  }

  // Float precision cleanup (fixes 0.1+0.2, and sin(pi) rounding errors)
  function cleanFloat(val) {
    if (Math.abs(val) < 1e-14) return 0;
    // Limit precision decimal errors
    return parseFloat(val.toFixed(14));
  }

  // --- Auto-Correction & Safety ---
  function autoCorrectExpression(str) {
    let s = str.trim();
    if (!s) return "";

    // 1. Trim trailing open operators that are dangling
    while (/[+\-*/%^]$/.test(s) || /−$/.test(s) || /×$/.test(s) || /÷$/.test(s)) {
      s = s.slice(0, -1).trim();
    }

    // 2. Auto-close unmatched parentheses
    let openParenCount = 0;
    let closeParenCount = 0;
    for (let char of s) {
      if (char === '(') openParenCount++;
      if (char === ')') closeParenCount++;
    }

    if (openParenCount > closeParenCount) {
      s += ')'.repeat(openParenCount - closeParenCount);
    }

    return s;
  }

  // ==========================================================================
  // 2. CORE CALCULATOR OPERATIONS
  // ==========================================================================

  function handleInput(val) {
    // If a result was just evaluated, typing a digit resets the display
    if (lastEvaluated) {
      if (/[0-9.eπ]/.test(val) || val === 'pi') {
        expression = '';
      } else if (['+', '−', '×', '÷', '^', '%'].includes(val)) {
        // Carry over the last result to chain calculations
        expression = lastResult !== null ? lastResult.toString() : '';
      }
      lastEvaluated = false;
    }

    // Edge-case: prevent double decimal points in a single number token
    if (val === '.') {
      const tokens = expression.split(/[^0-9.]/);
      const currentNumberToken = tokens[tokens.length - 1];
      if (currentNumberToken.includes('.')) return;
    }

    expression += val;
    updateDisplay();
  }

  function handleClear() {
    expression = '';
    lastResult = null;
    lastEvaluated = false;
    updateDisplay();
  }

  function handleBackspace() {
    if (lastEvaluated) {
      expression = '';
      lastEvaluated = false;
      updateDisplay();
      return;
    }

    if (expression.length === 0) return;

    // Premium touch: Deleting full functional words like 'sin(', 'cos(', etc.
    const functionsList = ['sin(', 'cos(', 'tan(', 'log(', 'ln(', 'sqrt('];
    let deletedWord = false;

    for (let func of functionsList) {
      if (expression.endsWith(func)) {
        expression = expression.slice(0, -func.length);
        deletedWord = true;
        break;
      }
    }

    if (!deletedWord) {
      expression = expression.slice(0, -1);
    }

    updateDisplay();
  }

  function handleNegation() {
    if (lastEvaluated) {
      expression = lastResult !== null ? lastResult.toString() : '';
      lastEvaluated = false;
    }

    if (!expression) {
      expression = '−';
      updateDisplay();
      return;
    }

    // Match the last number token in the expression (allowing decimals and minus sign)
    const match = expression.match(/([−-]?[0-9.]+)$/);
    if (match) {
      const numStr = match[1];
      const index = expression.lastIndexOf(numStr);
      let negated;

      if (numStr.startsWith('−') || numStr.startsWith('-')) {
        negated = numStr.slice(1);
      } else {
        negated = '−' + numStr;
      }
      expression = expression.slice(0, index) + negated;
    } else {
      // If there's no trailing number, append a minus sign
      expression += '−';
    }
    updateDisplay();
  }

  function handleScientificAction(action) {
    if (lastEvaluated) {
      if (action === 'square' || action === 'recip' || action === 'fact') {
        expression = lastResult !== null ? lastResult.toString() : '';
      } else {
        expression = '';
      }
      lastEvaluated = false;
    }

    switch (action) {
      case 'sin':
      case 'cos':
      case 'tan':
      case 'log':
      case 'ln':
        expression += action + '(';
        break;
      case 'square':
        expression += '^2';
        break;
      case 'recip':
        expression += '^-1';
        break;
      case 'fact':
        expression += '!';
        break;
    }
    updateDisplay();
  }

  function handleEvaluate() {
    if (!expression.trim()) return;

    const originalExpr = expression;
    const correctedExpr = autoCorrectExpression(expression);

    if (!correctedExpr) {
      showToast('Empty or incomplete expression');
      return;
    }

    try {
      // 1. Tokenize
      const rawTokens = tokenize(correctedExpr);
      
      // 2. Optimise with Implicit Multiplication
      const processedTokens = insertImplicitMultiplication(rawTokens);
      
      // 3. Parse AST
      const parser = new Parser(processedTokens);
      const ast = parser.parse();

      // 4. Evaluate AST
      const result = evaluateAST(ast);

      // Save states
      lastResult = cleanFloat(result);
      
      // Update screens
      expressionScreen.textContent = originalExpr + ' =';
      inputScreen.textContent = formatResult(lastResult);
      
      // Save to History
      addHistoryItem(originalExpr, lastResult);

      expression = lastResult.toString();
      lastEvaluated = true;
      
      // Reset horizontal scroll to right
      setTimeout(() => {
        inputScreen.scrollLeft = inputScreen.scrollWidth;
      }, 50);

    } catch (error) {
      console.error(error);
      showToast(error.message || 'Calculation Error');
      // Highlight the display with error styling momentarily
      inputScreen.classList.add('error-shimmer');
      setTimeout(() => inputScreen.classList.remove('error-shimmer'), 500);
    }
  }

  // Formatting large/small numbers cleanly
  function formatResult(num) {
    if (num === Infinity) return 'Infinity';
    if (num === -Infinity) return '-Infinity';
    if (isNaN(num)) return 'NaN';

    const maxDigits = 14;
    const strVal = num.toString();

    // Exponential notation for extreme numbers
    if (Math.abs(num) > 1e12 || (Math.abs(num) < 1e-6 && num !== 0)) {
      return num.toExponential(7);
    }

    if (strVal.length > maxDigits) {
      if (Number.isInteger(num)) {
        return num.toExponential(7);
      } else {
        // Trim decimals appropriately
        return parseFloat(num.toFixed(10));
      }
    }

    // Replace standard hyphens with premium unicode minus in display
    return strVal.replace(/-/g, '−');
  }

  // ==========================================================================
  // 3. DISPLAY & FONT SIZE MANAGEMENT
  // ==========================================================================

  function updateDisplay() {
    // Set the expression screen content
    if (!lastEvaluated) {
      expressionScreen.textContent = expression;
    }

    // Set active input screen
    if (!expression) {
      inputScreen.textContent = '0';
    } else {
      inputScreen.textContent = expression;
    }

    // Manage Font Size dynamically to avoid layout breakage
    const displayLength = inputScreen.textContent.length;
    if (displayLength < 10) {
      inputScreen.style.fontSize = '3rem';
    } else if (displayLength < 14) {
      inputScreen.style.fontSize = '2.2rem';
    } else if (displayLength < 18) {
      inputScreen.style.fontSize = '1.7rem';
    } else {
      inputScreen.style.fontSize = '1.3rem';
    }

    // Scroll to the end of the text so users see active typing
    inputScreen.scrollLeft = inputScreen.scrollWidth;
  }

  // ==========================================================================
  // 4. THEME & ACCENT MANAGEMENT
  // ==========================================================================

  function initTheme() {
    const savedAccent = localStorage.getItem('calc-accent') || 'purple';
    setAccent(savedAccent);

    // Accent picker click handlers
    accentDots.forEach(dot => {
      dot.addEventListener('click', (e) => {
        const selectedAccent = e.target.getAttribute('data-accent');
        setAccent(selectedAccent);
      });
    });
  }

  function setAccent(accentName) {
    // Remove other accent classes
    document.body.classList.remove('accent-purple', 'accent-blue', 'accent-emerald', 'accent-rose');
    // Add selected accent
    document.body.classList.add(`accent-${accentName}`);
    
    // Update dots active states
    accentDots.forEach(dot => {
      if (dot.getAttribute('data-accent') === accentName) {
        dot.classList.add('active');
      } else {
        dot.classList.remove('active');
      }
    });

    localStorage.setItem('calc-accent', accentName);
  }

  // ==========================================================================
  // 5. MODE SWITCHER (Standard / Scientific Layout Toggling)
  // ==========================================================================

  modeStdBtn.addEventListener('click', () => {
    if (modeStdBtn.classList.contains('active')) return;
    toggleMode(false);
  });

  modeSciBtn.addEventListener('click', () => {
    if (modeSciBtn.classList.contains('active')) return;
    toggleMode(true);
  });

  function toggleMode(toScientific) {
    if (toScientific) {
      modeSciBtn.classList.add('active');
      modeStdBtn.classList.remove('active');
      scientificKeypad.classList.add('active');
      scientificKeypad.classList.remove('collapsed');
      appContainer.classList.add('scientific-active');
    } else {
      modeStdBtn.classList.add('active');
      modeSciBtn.classList.remove('active');
      scientificKeypad.classList.remove('active');
      scientificKeypad.classList.add('collapsed');
      appContainer.classList.remove('scientific-active');
    }
    // Resize display scroll alignment
    setTimeout(updateDisplay, 150);
  }

  // Degrees / Radians toggle
  degRadToggle.addEventListener('click', () => {
    isRadians = !isRadians;
    degRadToggle.textContent = isRadians ? 'Rad' : 'Deg';
    degRadToggle.classList.toggle('active', !isRadians);
    showToast(`Mode switched to ${isRadians ? 'Radians' : 'Degrees'}`);
  });

  // ==========================================================================
  // 6. HISTORY LOG DRAWER MANAGEMENT
  // ==========================================================================

  function initHistory() {
    const savedHistory = localStorage.getItem('calc-history');
    if (savedHistory) {
      history = JSON.parse(savedHistory);
    }
    renderHistory();
  }

  function addHistoryItem(expr, res) {
    // Format expression to look neat
    const item = { expression: expr, result: res };
    // Prepend to array
    history.unshift(item);
    // Limit to 20 items max
    if (history.length > 20) history.pop();
    
    localStorage.setItem('calc-history', JSON.stringify(history));
    renderHistory();
  }

  function renderHistory() {
    historyList.innerHTML = '';
    
    if (history.length === 0) {
      historyEmpty.style.display = 'flex';
      clearHistoryBtn.style.display = 'none';
      return;
    }

    historyEmpty.style.display = 'none';
    clearHistoryBtn.style.display = 'flex';

    history.forEach((item, index) => {
      const li = document.createElement('li');
      li.className = 'history-item';
      li.innerHTML = `
        <span class="history-expr">${item.expression}</span>
        <span class="history-res">${formatResult(item.result)}</span>
      `;
      li.addEventListener('click', () => {
        expression = item.expression;
        lastEvaluated = false;
        updateDisplay();
        closeHistory();
        showToast('Restored calculation');
      });
      historyList.appendChild(li);
    });
  }

  function clearHistory() {
    history = [];
    localStorage.removeItem('calc-history');
    renderHistory();
    showToast('History cleared');
  }

  function openHistory() {
    historyDrawer.classList.add('open');
  }

  function closeHistory() {
    historyDrawer.classList.remove('open');
  }

  historyBtn.addEventListener('click', openHistory);
  closeHistoryBtn.addEventListener('click', closeHistory);
  clearHistoryBtn.addEventListener('click', clearHistory);

  // Close drawer if user clicks outside of it
  document.addEventListener('click', (e) => {
    if (historyDrawer.classList.contains('open') && 
        !historyDrawer.contains(e.target) && 
        !historyBtn.contains(e.target)) {
      closeHistory();
    }
  });

  // ==========================================================================
  // 7. KEYBOARD INTEGRATION & FEEDBACK
  // ==========================================================================

  // Map physical keys to calculator buttons and actions
  const keyboardMap = {
    '0': { type: 'val', value: '0' },
    '1': { type: 'val', value: '1' },
    '2': { type: 'val', value: '2' },
    '3': { type: 'val', value: '3' },
    '4': { type: 'val', value: '4' },
    '5': { type: 'val', value: '5' },
    '6': { type: 'val', value: '6' },
    '7': { type: 'val', value: '7' },
    '8': { type: 'val', value: '8' },
    '9': { type: 'val', value: '9' },
    '.': { type: 'val', value: '.' },
    '+': { type: 'val', value: '+' },
    '-': { type: 'val', value: '−' },
    '*': { type: 'val', value: '×' },
    '/': { type: 'val', value: '÷' },
    '%': { type: 'val', value: '%' },
    '^': { type: 'val', value: '^' },
    '(': { type: 'val', value: '(' },
    ')': { type: 'val', value: ')' },
    'p': { type: 'val', value: 'π' },
    'P': { type: 'val', value: 'π' },
    'e': { type: 'val', value: 'e' },
    'E': { type: 'val', value: 'e' },
    '!': { type: 'sci', value: 'fact' },
    'Enter': { type: 'action', value: 'equals' },
    '=': { type: 'action', value: 'equals' },
    'Backspace': { type: 'action', value: 'backspace' },
    'Escape': { type: 'action', value: 'clear' }
  };

  document.addEventListener('keydown', (e) => {
    // Avoid interfering with browser shortcuts
    if (e.ctrlKey || e.metaKey || e.altKey) return;

    const mapped = keyboardMap[e.key];
    if (!mapped) return;

    e.preventDefault();

    // Trigger calculation actions
    if (mapped.type === 'val') {
      handleInput(mapped.value);
      animateKeyPress(mapped.value, 'val');
    } else if (mapped.type === 'sci') {
      handleScientificAction(mapped.value);
      animateKeyPress(mapped.value, 'sci');
    } else if (mapped.type === 'action') {
      if (mapped.value === 'equals') {
        handleEvaluate();
        animateKeyPress('equals', 'action');
      } else if (mapped.value === 'backspace') {
        handleBackspace();
        animateKeyPress('backspace', 'action');
      } else if (mapped.value === 'clear') {
        handleClear();
        animateKeyPress('clear', 'action');
      }
    }
  });

  // Animate buttons on physical keyboard presses for tactile premium feel
  function animateKeyPress(value, type) {
    let query = '';
    
    if (type === 'val') {
      // Find buttons by data-val attribute
      query = `.btn[data-val="${value}"]`;
    } else if (type === 'sci') {
      // Find by data-action attribute
      query = `.btn[data-action="${value}"]`;
    } else if (type === 'action') {
      query = `.btn[data-action="${value}"]`;
      if (value === 'clear') query = '#btn-clear';
    }

    const targetBtn = document.querySelector(query);
    if (targetBtn) {
      targetBtn.classList.add('keyboard-active');
      setTimeout(() => {
        targetBtn.classList.remove('keyboard-active');
      }, 100);
    }
  }

  // ==========================================================================
  // 8. CLICK/TOUCH LISTENERS (Mouse & Tap Inputs)
  // ==========================================================================

  // Delegate click events to keypad container
  document.querySelector('.calc-keypad-container').addEventListener('click', (e) => {
    const btn = e.target.closest('.btn');
    if (!btn) return;

    const val = btn.getAttribute('data-val');
    const action = btn.getAttribute('data-action');

    // Tap/Click haptic-feedback simulation
    btn.blur();

    if (val !== null) {
      handleInput(val);
    } else if (action !== null) {
      if (action === 'clear') {
        handleClear();
      } else if (action === 'backspace') {
        handleBackspace();
      } else if (action === 'negate') {
        handleNegation();
      } else if (action === 'equals') {
        handleEvaluate();
      } else {
        handleScientificAction(action);
      }
    }
  });

  // ==========================================================================
  // 9. UTILITIES (Toasts & Notifications)
  // ==========================================================================

  let toastTimeout;
  function showToast(msg) {
    toast.textContent = msg;
    toast.classList.add('show');
    
    clearTimeout(toastTimeout);
    toastTimeout = setTimeout(() => {
      toast.classList.remove('show');
    }, 2500);
  }
});
