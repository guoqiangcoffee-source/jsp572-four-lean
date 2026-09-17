# JSP-000572 四元情形：精确极值的 Lean 形式化

**郭强 · AI 辅助数学形式化项目 · 2026-09-17**

公开联系邮箱：[guoqiangcoffee@gmail.com](mailto:guoqiangcoffee@gmail.com)。

本项目完成了一个已知组合数学定理的 Lean 形式化：对每一个自然数 n，求出“不含恰好单元素交集的四元集合族”能够达到的最大大小，并证明上界及达到上界的构造。

| 底集元素数 n | 集合族的精确最大大小 |
|---|---|
| 0 ≤ n ≤ 6 | C(n, 4) |
| n = 7 | 15 |
| n = 8 | 17 |
| n ≥ 9 | C(n−2, 2) |

最终定理是 JSP572Four.jsp572_four_complete，位于 JSP572Four/Main.lean。它涵盖四元情形的全部规模。项目包含 23 个证明模块。

## 本次贡献与归属

- 郭强：项目发起、研究方向选择、公开发布；使用 OpenAI Codex 辅助完成本项目。
- OpenAI Codex：协助数学推导、Lean 代码实现、验证执行和文档整理。
- 原数学定理：Peter Keevash、Dhruv Mubayi、Richard M. Wilson，2006 年论文 Theorem 1.1 的数值部分。本项目贡献是形式化与验证，不主张发现新的数学定理。
- mathlib 及其依赖：证明库支持；改编代码及原作者详见 AUTHORS.md。

数学原文：[Set Systems with No Singleton Intersection](https://doi.org/10.1137/050647372)，SIAM Journal on Discrete Mathematics 20(4), 1031–1041；[作者提供的论文](https://people.maths.ox.ac.uk/keevash/papers/no-singleton-journal.pdf)。

## 已完成的核验

Lean 编译、内核复核和公理审计已经通过。最终定理只依赖 Lean 常用的三个基础公理：propext、Classical.choice、Quot.sound。项目证明没有 sorry、admit、自定义未证数学公理或 native_decide。

此外，导出的完整证明依赖由 lean4lean 和 nanoda 两套独立实现的检查器检查通过。lean4lean 检查了 8,283 条声明，另有上述三个允许的基础公理。核验在本地执行；完整记录及复现边界见 VERIFICATION.md。

## 复现

Lean：leanprover/lean4:v4.35.0-rc2。mathlib 固定为 f61f3ed7633ff99ecaae4a086395b501652a76ee，依赖版本见 lake-manifest.json。

安装对应 Lean 工具链和 Git，在项目目录执行：

~~~text
lake exe cache get
lake build JSP572Four
lake env lean Audit.lean
~~~

Windows 可使用 verify.ps1；验证导出与独立检查说明见 verification/。本次公开包仅更新署名和发布说明，23 个证明模块及已验证的证明导出与先前核验版本一致。

## 范围

这是与 JSP-000572 相关的 **k=4 精确结果**，不是一般 k≥4 的原题形式化，也不包含极值构造的唯一性分类。

源码与验证材料已在 [guoqiangcoffee-source/jsp572-four-lean](https://github.com/guoqiangcoffee-source/jsp572-four-lean) 公开。郭强正在准备正式提交，提请主办方评审，并如实披露四元范围及既有工作。

按 2026-09-17 核查到的官方规则，投稿须覆盖完整原题，单独特例不符合该要求；本项目存在这一范围限制。提交不等于获得资格、受理或获奖，也不主张首次形式化优先权。目前尚未收到接受决定，贡献认定及奖项决定由评审方作出。详见 CURRENT-INTAKE.md 与 PRIORITY-REVIEW.md。

## English abstract

An AI-assisted Lean formalization led by Guo Qiang of the numerical four-uniform theorem of Keevash, Mubayi and Wilson (2006). For every ground-set size, it proves the sharp upper bound and supplies an attaining family. The final theorem passed Lean checking, an explicit axiom audit, and independent lean4lean and nanoda checks. Mathematical discovery credit belongs to the original authors. This package does not claim the general JSP-000572 result, first formalization priority, equality-case classification, or prize recognition.

License: Apache-2.0. See LICENSE and AUTHORS.md.
