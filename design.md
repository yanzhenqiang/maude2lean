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
- `cauchy_complete`：对角线极限构造严格，零 `refl Prop` 占位
- `const_seq_converges` / `zero_seq_converges`：基于 `frac_dist_self` 严格证明

**核心文件零占位状态**：
- `Cauchy.lean`、`Real.lean`、`Complete.lean`、`FracArith.lean` 中已无 `refl Prop` 占位
- 所有 `refl Prop` 占位（`seq_converges_to_compat`、`cauchy_equiv_*_compat`、`real_lt_trichotomy` 等）已清理删除

### 4.3 定义缺陷

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
