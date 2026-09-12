# 无元层选择的 ZF 研究证据

这些文件保存已通过 Lean 核验的构造、条件秩和架构边界；完整 ZF 模型仍未完成。
普通观察、稳定观察和描述树是三套候选，不能把各自性质合成一个尚未证明的模型。
结果、必要超额增量及下一步义务见[研究记录](../../markdown/CHOICE_FREE_ZF_RESEARCH.md)。

从仓库根目录先运行 `lake --wfail build`，再显式检查需要的研究文件，例如：

```powershell
lake env lean -DwarningAsError=true -DrelaxedAutoImplicit=false research/ChoiceFreeZF/semantics-church-stable.lean
```

这里没有默认库入口；文件均独立核验，不互相依赖。所有关键端点的依赖最多为
`propext`、`Quot.sound`。逐文件摘要、源码指纹和实际行数见 [verification.json](verification.json)。
