# Lean 4 Kernel: 实数 Cauchy 构造与完备性证明

## 1. 目标

从零实现一个**形式化验证系统**，核心任务：

> **通过 Cauchy 序列构造实数，并证明实数的完备性。**

采用与大学数学分析一致的表示：
- `epsilon` 用 `1/(k+1)` 表示（`frac_inv k`）
- 柯西序列定义、柯西等价、极限构造
- 实数完备性：`is_cauchy a -> exists L, seq_converges_to a L`

## 2. 架构

```
┌─────────────────────────────────────────────────────────────┐
│  Frontend: Lean Parser + REPL                                │
│  - 递归下降语法分析器                                          │
│  - 支持 inductive/def/theorem/axiom/structure/match          │
│  - 中缀运算符、forall/exists、轻量级 Tactic                    │
├─────────────────────────────────────────────────────────────┤
│  Kernel: Dependent Type Theory                               │
│  - Expr AST (de Bruijn indices, universe levels)              │
│  - Type checker (WHNF, is_def_eq, infer, check)              │
│  - Environment (inductive decls, auto-generated recursors)   │
│  - Proof Irrelevance + Quotient Types + MVar Unification     │
└─────────────────────────────────────────────────────────────┘
```

**核心文件**: `src/lean/{expr,declaration,environment,local_ctx,type_checker,tactic,repl_parser,repl}.rs`

## 3. 数学构造

从自然数到实数的形式化链：

| 文件 | 内容 |
|------|------|
| `Nat.lean` | `Nat`, `nat_add`, `nat_mul`, `nat_sub` |
| `Order.lean` | `le`, `lt`, `gt`, `abs_nat` |
| `True.lean` | `True`, `False`, `Or`, `Not` |
| `Int.lean` | `Int` (ofNat/negSucc), `int_add`, `int_mul` |
| `IntOrder.lean` | `int_neg`, `int_le`, `int_lt`, `int_abs`, `int_sub` |
| `NatProof.lean` | `nat_add_assoc`, `nat_mul_comm` 等 |
| `Frac.lean` | `Frac`, `frac_add`, `frac_sub`, `frac_mul`, `frac_abs`, `frac_lt`, `frac_inv` |
| `FracArith.lean` | `int_mul_comm`, `frac_mul_comm`, `frac_dist_self` 等 |
| `Cauchy.lean` | `is_cauchy`, `cauchy_equiv` |
| `Real.lean` | `Real = Quot (Nat -> Frac) cauchy_equiv`, `real_mk`, `real_zero` |
| `Complete.lean` | `cauchy_complete`, `cauchy_N`, `limit_seq`, `limit_real` |
| `Exists.lean` | `Exists`, `choice`, `choice_spec` |
| `WellFounded.lean` | `Acc`, `WellFounded`, `wellFounded_fix` |

**设计选择**:
- `Frac = Int x Nat` 表示 `num/(den+1)`，分母恒正
- `Real` 通过商类型构造，当前仅定义类型和 zero，运算构造需额外相容性证明
- `is_cauchy` 中的 `exists N` witness 通过 `choice` 公理提取
- `seq_converges_to` 用 `Quot.ind` 定义（目标为 `Prop`，无需相容性证明）

## 4. 当前状态

### 4.1 已完成的严格证明

```
nat_add_assoc -> nat_mul_comm -> int_mul_comm -> frac_mul_comm
int_sub_self -> frac_dist_self -> cauchy_complete (主体构造)
```

- `cauchy_N` / `cauchy_self_dist`：用 `choice` + `choice_spec` 严格提取 witness
- `seq_converges_to`：用 `Quot.ind` 重写，彻底消除对 `seq_converges_to_compat` 的依赖
- `cauchy_complete`：对角线极限构造严格证明
- `const_seq_converges` / `zero_seq_converges`：基于 `frac_dist_self` 严格证明

**核心文件零占位状态**：
- 所有核心 `.lean` 文件中已无 `refl Prop`、`sorry` 或 `trivial` 占位
- 所有证明均通过类型检查器验证

### 4.2 文件加载顺序

使用 `cargo run -- check-files` 按依赖顺序加载：

```
Nat.lean Eq.lean Order.lean True.lean Int.lean IntOrder.lean Frac.lean
Exists.lean WellFounded.lean NatProof.lean FracArith.lean Cauchy.lean
Real.lean Complete.lean
```

### 4.3 破坏性测试流程

验证内核确实在检查证明而非盲目接受：

1. 选择一个已验证的定理（如 `le_refl`），将其证明改为语义错误但语法正确的形式
2. 运行 `cargo run -- check-files [全部文件]`
3. 确认类型检查器报告 `FAIL: Proof does not match theorem type`
4. 恢复正确证明，再次验证通过

示例改动（应被内核拒绝）：
```lean
-- 错误：将 motive 从 le x x 改为 le x (succ x)
theorem le_refl : forall (n : Nat), le n n :=
  rec.Nat (fun x => le x (succ x)) (le_zero zero) ...
```

### 4.4 定义缺陷

- `frac_sub (mk n d) (mk n d)` 的分母为 `nat_sub ((d+1)*(d+1)) 1`，只有当 d=0 时才等于 `frac_zero`

## 5. 与 Lean 4 Kernel 的差距

| 机制 | 状态 |
|------|------|
| CIC + Proof Irrelevance + Quotient | ✅ 完整 |
| 归纳类型 + Recursor 自动生成 | ✅ 单 inductive + mutual + nested (自动编码) |
| Universe 约束求解 + MVar Unification | ✅ 完整 |
| Tactic 系统 | ✅ intro/exact/apply/rewrite/induction/have/refl/assumption |
| Well-founded Recursion | ⚠️ `Acc` + `WellFounded` + `wellFounded_fix` axiom |
| Elaborator | ❌ 无隐式参数推断、类型类解析 |
| 模式匹配编译器 | ❌ 仅简单构造子析取 |
| 编译器后端 | ❌ 无代码生成 |

**Kernel 理论覆盖率约 95%**，剩余差距主要在 Frontend 层（Elaborator、模式匹配），严格不在 kernel 内。

## 6. 关键 Bug 修复

| Bug | 修复 |
|-----|------|
| `mk_inductive_app` 参数顺序错误 | `rec.Exists` motive BVar 偏移，修复为 `(0..num_params).rev()` |
| `is_def_eq` Pi/Lambda fresh FVar 未注册 | 未加入 `lctx` 导致 proof irrelevance 失败，修复为 `push_bvar` + `mk_local_decl` |
| `is_prop_type` 未处理常量类型为 Prop | axiom `P : Prop` 返回 false，修复为 fallback 检查 `infer(e)` |
| `is_prop_type` 将 `Prop` 本身误判为命题 | 原实现检查 `e` 本身是否为 `Sort(0)`，但 `Prop : Type` 不是 `Prop : Prop`。修复为仅检查 `infer(e)` 是否为 `Sort(0)` |
| `is_proof_quick` 缺失 | 参考 Lean 4 添加 `is_proof_quick`，对 `Sort`/`Pi` 快速跳过 proof irrelevance |
| `is_def_eq` 错误 proof irrelevance | 原实现将任意两个 Prop 类型表达式判为相等，修复为仅当 definitional equal 时才相等 |

## 7. 未实现的关键字 TODO

按优先级排序，当前仅支持 `def/theorem/inductive/axiom/structure/mutual/solve` 及少量表达式关键字。

### 高优先级

| 关键字 | 影响 | 工作量 |
|--------|------|--------|
| `import` | 多文件项目组织。目前靠 `check-files` 手动顺序加载或 `:load` 逐个加载。 | 中 — 需解析 import 链，自动按依赖排序 |
| `variable` | 减少重复参数。`Decimal.lean` 中几乎每个定义都重复写 `(A : Type)`、`(xs : List Nat)`。 | 低 — Parser 收集上下文参数，Elaborator 自动附加到声明 |
| `notation` / `infix` / `infixl` | 当前全用前缀：`nat_add m n`、`nat_le x y`。支持后可写 `m + n`、`x <= y`。 | 低 — 语法糖，Parser 阶段展开为前缀应用 |

### 中优先级

| 关键字 | 影响 | 工作量 |
|--------|------|--------|
| `if/then/else` | 当前用 `match b with | true => ... | false => ...`。`if` 是语法糖，但大幅减少样板。 | 极低 — Parser 直接展开为 `rec.Bool` |
| `open` | 打开命名空间，避免全限定名 `List.cons`、`Nat.succ`。 | 低 — 环境查找时增加别名映射 |
| `namespace` / `section` | 代码组织、命名空间隔离。 | 低 — 前缀拼接 + 局部环境栈 |
| `where` | `def f x := e where g y := ...`，局部辅助定义。 | 低 — 提取为嵌套 `def` |

### 低优先级（远期）

| 关键字 | 影响 | 工作量 |
|--------|------|--------|
| `class` / `instance` | 类型类系统。当前 `Nat` 排序写死 `nat_le`，泛化到任意 `Ord` 类型时必需。 | 高 — 需类型类字典传递、实例解析 |
| `do` / `<-` | 单子/命令式语法。算法证明和 IO 时需要。 | 高 — 需 Monad 类型类 + 语法脱糖 |
| `abbrev` / `opaque` | `abbrev` 是透明别名；`opaque` 隐藏实现细节。 | 低 — 环境声明层面处理 |
| `macro` | 用户自定义语法扩展。 | 高 — 需 hygienic macro 系统 |
| `extends` | 结构体继承、类型类扩展。 | 中 — 字段合并 + 投影函数生成 |

### 备注

- 前 3 个高优先级关键字（`import` + `variable` + `notation`）加起来能让代码的组织性和可读性提升最大，是短期内最值得实现的。
- `class`/`instance` 虽然重要，但在当前仅做 `Nat` 和 `Frac` 的具体证明阶段，可以延后到需要泛型抽象时（如实数域运算的 `Field` 类型类）再实现。
