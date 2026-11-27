# 平方根主弧环带二阶矩 · 换机接续

截至 2026-11-27，完整证明已保存到 `zxg0623/goldbach-proofs`。项目固定的 Lean 4.36.0 与本地 `checklemma` 已核对冻结命题，内核重查 1119 个常量，使用 `propext`、`Classical.choice`、`Quot.sound`。项目的导入检查及依赖闭包检查也已通过。[冻结命题](statement.txt) · [本地核验原始输出](checklemma.log)

对每个充分大的自然数 $n$，只在平方根主弧内、立方根宽主弧外的区域积分，素数对数权指数和的无符号二阶矩就至少有 $c n\log n$，其中 $c>0$ 与 $n$ 无关。证明使用 $n^{1/3}<q\le n^{5/12}$ 的平方自由分母，在每个既约分数右侧取宽 $1/(6n)$ 的小窗。小窗位于目标区域，其贡献相加即可得到下界。

| 内容 | 保存位置 |
| --- | --- |
| 可继续开发的单文件证明分支 | [proof/sqrt-shell-second-moment-floor](https://github.com/zxg0623/goldbach-proofs/tree/proof/sqrt-shell-second-moment-floor) |
| 已核对的证明版本 | [68046964](https://github.com/zxg0623/goldbach-proofs/commit/68046964ae1bdceb79bc22633eb72f099d160842) |
| 命题目录分支 | [research/sqrt-shell-second-moment-floor](https://github.com/zxg0623/goldbach-proofs/tree/research/sqrt-shell-second-moment-floor) |
| 上游命题草稿 | [#3745](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3745) |
| 证明依赖 | [已合并的 #3727](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3727) |

## 在另一台电脑打开证明

```sh
git clone --branch proof/sqrt-shell-second-moment-floor https://github.com/zxg0623/goldbach-proofs.git
cd goldbach-proofs
git log -1 --oneline
```

证明文件位于 `lean/Conjectures/Goldbach/SqrtShellSecondMomentFloor.lean`。下载后可与上述提交逐字节核对，Git 中的文件使用 LF 换行。

| 核对项 | 值 |
| --- | --- |
| 研究台命题 | `L-goldbach-sqrt-shell-second-moment-floor` |
| 证明文件 SHA-256 | `ed7a5bca3750a288de89b9dd6ea5ed8bfcf8c704ec8e3d0c62de8f7970b0491f` |
| 冻结命题 SHA-256 | `8b8ac79632a3ff037766529a761c097afc271d0cdef0edda2d476c117c23910f` |

## 暂停位置

上游 #3745 在暂停前已经打开，现已转回草稿。证明只推送到个人仓库。本次没有创建上游证明 PR，没有领取任务，也没有启动研究台正式核验。

以后决定送检时，先检查 #3745 的状态和命题是否有变。按上游流程恢复目录审阅，等命题发布到研究台后，用 `zxg0623` 领取该命题，从上述单文件证明分支取回源码，再按项目指南创建证明 PR 并登记核验。[上游参与指南](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/main/CONTRIBUTING.md)
