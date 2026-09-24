import YesMetaZFC.Logic.Arithmetic.Z2.Axioms

/-! # 从完整理解导出全公式归纳

先对 φ 的外延集合使用集合归纳，再经逐点等价传回 φ。
替换证明保留任意混合参数；不借用标准模型真值或完备性。
-/
namespace YesMetaZFC.Logic.Arithmetic.Z2
open FirstOrder
set_option autoImplicit false

private theorem inst {Δ : SortContext signature_m} {T : Theory signature_m}
    {Γ : Context signature_m Δ} {φ : Formula signature_m [] (.num :: Δ)}
    (t : Term signature_m [] Δ .num) (h : Derives T Γ (φ.forallFreeTop sort_m.num)) :
    Derives T Γ (φ.instantiateFreeTop t) := by
  simpa only [Formula.forallFreeTop, Formula.instantiateTop_abstractFreeTop] using
    Derives.forall_elim t h

private theorem insert_zero {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) :
    (insert_m φ).instantiateFreeTop zero_m =
      (φ.instantiateFreeTop zero_m).weakenFree sort_m.set := by
  change (φ.renameMapped _ _).substituteMapped _ _ =
    (φ.substituteMapped _ _).renameMapped _ _
  rw [← Formula.substituteMapped_of_renaming, ← Formula.substituteMapped_of_renaming,
    Formula.substituteMapped_comp, Formula.substituteMapped_comp]
  congr 1
  funext s v
  cases v <;> rfl

private theorem insert_next {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) :
    (insert_m φ).substituteFree next_m = insert_m (φ.substituteFree next_m) := by
  change (φ.renameMapped _ _).substituteMapped _ _ =
    (φ.substituteMapped _ _).renameMapped _ _
  rw [← Formula.substituteMapped_of_renaming, ← Formula.substituteMapped_of_renaming,
    Formula.substituteMapped_comp, Formula.substituteMapped_comp]
  congr 1
  funext s v
  cases v <;> rfl

private theorem insert_forall {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) :
    (insert_m φ).forallFreeTop sort_m.num =
      Formula.weakenFree (σ := signature_m) sort_m.set (φ.forallFreeTop sort_m.num) := by
  exact (Formula.renameMapped_forallFreeTop (σ := signature_m)
    (VariableRenaming.weaken sort_m.set) φ).symm

private theorem insert_induction {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) :
    induction_m (insert_m φ) = (induction_m φ).weakenFree sort_m.set := by
  simp only [induction_m, insert_zero, insert_forall, insert_next]
  change Formula.imp _ _ = Formula.imp _ _
  congr 2
  exact insert_forall (.imp φ (φ.substituteFree next_m))

private theorem next_eq {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) :
    (φ.abstractFreeTop.weakenFree sort_m.num).instantiateTop (succ_m (.fvar .here)) =
      φ.substituteFree next_m := by
  change ((φ.substituteMapped _ _).renameMapped _ _).substituteMapped _ _ =
    φ.substituteMapped _ _
  rw [← Formula.substituteMapped_of_renaming, Formula.substituteMapped_comp,
    Formula.substituteMapped_comp]
  congr 1
  all_goals
    funext s v
    cases v <;> rfl

private theorem inst_next {Δ : SortContext signature_m} {T : Theory signature_m}
    {Γ : Context signature_m Δ} {φ : Formula signature_m [] (.num :: Δ)}
    (h : Derives T Γ (φ.forallFreeTop sort_m.num)) :
    Derives T (FreshVariable.extendContext sort_m.num Γ) (φ.substituteFree next_m) := by
  have h₁ := Derives.free_renaming (VariableRenaming.weaken sort_m.num) h
  have h₂ := Derives.forall_elim (succ_m (.fvar .here)) h₁
  simp only [VariableRenaming.lift_id] at h₂
  change Derives T _ ((φ.abstractFreeTop.weakenFree sort_m.num).instantiateTop _) at h₂
  rwa [next_eq] at h₂

/-- 逐点可证等价保持归纳实例；这里不要求 T 含任何算术公理。 -/
theorem induction_congr_m {Δ : SortContext signature_m} {T : Theory signature_m}
    {Γ : Context signature_m Δ} {φ ψ : Formula signature_m [] (.num :: Δ)}
    (h : Derives T Γ ((Formula.iff φ ψ).forallFreeTop sort_m.num))
    (hᵢ : Derives T Γ (induction_m φ)) : Derives T Γ (induction_m ψ) := by
  apply Derives.imp_intro
  let θ := Formula.conj (ψ.instantiateFreeTop zero_m)
    ((Formula.imp ψ (ψ.substituteFree next_m)).forallFreeTop sort_m.num)
  have h₀ := Derives.context_weaken_cons (assumption := θ) h
  have h₁ : Derives T (θ :: Γ) (ψ.instantiateFreeTop zero_m) :=
    Derives.conj_elim_left (Derives.assumption List.mem_cons_self)
  have h₂ : Derives T (θ :: Γ)
      ((Formula.imp ψ (ψ.substituteFree next_m)).forallFreeTop sort_m.num) :=
    Derives.conj_elim_right (Derives.assumption List.mem_cons_self)
  have h₃ : Derives T (θ :: Γ) (φ.instantiateFreeTop zero_m) :=
    Derives.iff_elim_right (inst zero_m h₀) h₁
  have h₄ : Derives T (θ :: Γ)
      ((Formula.imp φ (φ.substituteFree next_m)).forallFreeTop sort_m.num) := by
    apply Derives.forall_intro
    apply Derives.imp_intro
    have h₅ := Derives.context_weaken_cons (assumption := φ)
      (Derives.forall_elim_newest h₀)
    have h₆ := Derives.iff_elim_left h₅ (Derives.assumption List.mem_cons_self)
    have h₇ := Derives.imp_elim
      (Derives.context_weaken_cons (Derives.forall_elim_newest h₂)) h₆
    exact Derives.iff_elim_right (Derives.context_weaken_cons (inst_next h₀)) h₇
  have h₅ := Derives.imp_elim (Derives.context_weaken_cons hᵢ) (Derives.conj_intro h₃ h₄)
  apply Derives.forall_intro
  exact Derives.iff_elim_left (Derives.forall_elim_newest h₀) (Derives.forall_elim_newest h₅)

private theorem mem_induction {Δ : SortContext signature_m} {T : Theory signature_m}
    (hZ₂ : Theory.Extends T theory_m) {Γ : Context signature_m (.set :: Δ)} :
    Derives T Γ (induction_m (mem_m (.fvar .here) (.fvar (.there .here)))) := by
  have h : Derives T Γ (Formula.fromSentence set_induction_m) :=
    Derives.theory_axiom (hZ₂ axiom_m.set_induction)
  exact Derives.forall_elim (.fvar .here) h

/-- 完整公式归纳是实际对象推导，对任意扩张及局部上下文均成立。 -/
theorem induction_derives_m {T : Theory signature_m} (hZ₂ : Theory.Extends T theory_m)
    {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (φ : Formula signature_m [] (.num :: Δ)) : Derives T Γ (induction_m φ) := by
  have h₀ := comprehension_derives_m hZ₂ (Γ := []) φ
  have h₁ : Derives T [] (induction_m φ) := by
    apply Derives.exists_elim h₀
    rw [← insert_induction]
    exact induction_congr_m (Derives.assumption List.mem_cons_self) (mem_induction hZ₂)
  exact Derives.of_provable h₁

theorem induction_rule_m {T : Theory signature_m} (hZ₂ : Theory.Extends T theory_m)
    {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    {φ : Formula signature_m [] (.num :: Δ)}
    (h₀ : Derives T Γ (φ.instantiateFreeTop zero_m))
    (h₁ : Derives T (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next_m))) : Derives T Γ (φ.forallFreeTop sort_m.num) :=
  Derives.imp_elim (induction_derives_m hZ₂ φ) (Derives.conj_intro h₀ (Derives.forall_intro h₁))

end YesMetaZFC.Logic.Arithmetic.Z2
