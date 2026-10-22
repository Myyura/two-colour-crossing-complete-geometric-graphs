# 完整几何图边二染色交叉最小化的 NP 困难性

**Myyura** · **The Kai Project** · [English](README.md)

本仓库整理固定完整几何图边二染色交叉最小化问题阈值判定版本的 NP 完全性证明、Lean 证明及可复现的有限诊断计算。

输入是二进制编码的互异有理点，无三点共线，并给定整数阈值。固定直线完整图的每条边都可以自由选择两种颜色之一；目标计数为同色且严格内部交叉的无序边对数。整数坐标限制下结论仍成立，精确最小化问题为 NP-hard。

**项目地址：** [GitHub 仓库](https://github.com/Myyura/two-colour-crossing-complete-geometric-graphs) · [CI 运行记录](https://github.com/Myyura/two-colour-crossing-complete-geometric-graphs/actions/workflows/verify.yml)。论文尚未提交 arXiv。下文核验记录描述初次本地运行；当前 CI 结果见上述链接。

## 阅读入口

| 文件 | 内容 |
|---|---|
| [论文](paper/manuscript.pdf) · [LaTeX 源码](paper/tex/main.tex) | 完整数学证明与参考文献。 |
| [定理与范围](docs/theorem.md) | 精确输入、量词、规约及外部定理。 |
| [证明导读](docs/proof-guide.md) | 论证结构与 Lean 模块对应。 |
| [有效规约](docs/effective-reduction.md) | 确定性构造、位复杂度与可计算阈值。 |
| [形式化范围](docs/formalization.md) · [Lean 复现说明](lean/README.md) | 最终声明、验证入口及信任边界。 |
| [核验摘要](audit/README.md) · [来源说明](docs/provenance.md) | 实际检查范围及论文与形式化的关系。 |
| [有限诊断计算](computations/README.md) | 精确有限检查及其适用范围。 |

规约只输出一个完整图实例，计入所有补全边和跨类费用。最终形式化采用保守局部界 `2SW^4` 和严格间隔 `2^18(E_- + E_+) < Δ`。

## Lean 实际证明的内容

最终声明为

```text
Q4.Candidate.ConstructedReduction.constructed_maxcut_instance
```

它对同一组有理坐标证明完整自由边染色的阈值等价、坐标单射、无三点共线，以及点数和坐标的多项式界。它明确接受外部证书

```text
∀ m, ConvexOptimum m (knownZ m)
```

这一证书由已知完整图两页交叉数定理提供；源困难性由附排列表示的排列图 MaxCut 定理提供。两项结果的准确来源见[定理说明](docs/theorem.md#the-two-external-results)。

已保存的本地核验使用 **Lean 4.34.1** 和锁定的 mathlib 依赖，构建并逐文件重核了 **128 份 Lean 源码**。**883 次公理查询覆盖 882 个不同声明**，实际报告的依赖仅为 `propext`、`Classical.choice`、`Quot.sound`，详见[机器可读记录](lean/verification-summary.json)。这些是源码和选定查询的核验数，不表示逐条审计了工程中的每个声明。

机器运行时间、NP 成员资格、源困难性、外部凸最优值和单列目标阈值位界没有在本工程中重证为 Lean 复杂性类定理。有效规约的文字证明补充了 `O(N^7)` 次精确运算、中间位长多项式，以及 `|K| ≤ 32N^20(|k| + 1)`。核验信任 Lean 运行时、内核和锁定依赖的构建产物，没有从源码重建全部 mathlib。

## 目录结构

公开文件保留正常结构：`paper/` 保存论文，`lean/` 保存证明工程，`computations/` 保存有限检查，`docs/` 保存说明，`audit/` 保存公开核验记录。非公开材料实体集中在被忽略的 `.local/` 下：

| 目录 | 本地内容 |
|---|---|
| `.local/arxiv/` | 可选投稿元数据及生成的源码、PDF 和投稿包。 |
| `.local/research/` | 旧研究说明、脚本、结果、参考材料和历史 Lean 工程，保留原有相对目录结构。 |
| `.local/build/` | 构建产物、依赖缓存、新核验日志和导出压缩包。 |

在维护中的本地工作区，`lean/.lake` 和 `lean/build` 是指向 `.local/build/lean/` 内部的被忽略兼容符号链接，原有 Lean 命令仍可使用。本地材料及这些符号链接不进入公开源码包。

## 复现与打包

复验已保存的发行包时，在仓库根目录使用 Python 3.10 或更新版本运行：

```bash
python3 tools/repository.py check
python3 computations/run_checks.py
python3 lean/verify.py
```

第一条命令检查公开包与清单。有限诊断计算只使用 Python 标准库。Lean 核验还需要 elan、锁定工具链和依赖，初始化方法见 [Lean 说明](lean/README.md)。默认核验结果仍通过 `lean/build/verification/` 访问；在维护中的本地工作区，兼容符号链接使其实体保存在 `.local/build/lean/` 下，已发布的核验摘要保持不变。

维护者重建论文应在 Git checkout 中先运行：

```bash
python3 tools/build_paper.py
```

这需要支持的 LaTeX 引擎：`latexmk`、`pdflatex` 或 `tectonic`。检查重新生成的[论文 PDF](paper/manuscript.pdf)后，再有意更新发行记录：

```bash
python3 tools/repository.py refresh
python3 tools/repository.py export
```

重建可能改变 PDF 元数据及其哈希。`refresh` 会重新记录已检查的公开文件，并且要求 Git checkout；它不是原发行包复验的一部分。导出命令验证文件清单和编译绑定后，在 `.local/build/releases/` 下生成 `github.zip` 与 `public-source.tar.gz`，不会上传或投稿。

可选的本地投稿版本可以使用被忽略的 `.local/arxiv/metadata.json` 中的独立元数据。运行 `python3 tools/build_paper.py --edition arxiv` 后，该版本的源码、PDF 和投稿压缩包都保存在被忽略的 `.local/arxiv/` 目录，不进入公开导出包。

[CI 配置](.github/workflows/verify.yml)在一个 job 中运行公开包检查和有限计算，在另一个 job 中通过[官方 Lean Action](https://github.com/leanprover/lean-action)准备环境并运行本仓库的完整验证器。它使用官方 mathlib 缓存，禁用 GitHub 工程缓存复用。最新结果见 [GitHub Actions](https://github.com/Myyura/two-colour-crossing-complete-geometric-graphs/actions/workflows/verify.yml)；上文保存的成功核验来自初次本地运行。

## 署名与许可

作者为 **Myyura**，单位为 **The Kai Project**，引用元数据见 [CITATION.cff](CITATION.cff)。代码，包括 Lean 工程和验证脚本，使用 **Apache-2.0**；论文及配套论文说明使用 **CC BY 4.0**。具体范围和完整条款见[许可说明](LICENSE)。

本工作使用 AI 辅助，并包含分开的 LLM 审阅会话。这些审阅不是外部人类同行评审；有限计算通过也不替代全称数学证明或准确的形式化范围说明。
