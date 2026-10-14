import YesMetaZFC.SetTheory.LargeCardinal.IterationWellFounded
import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.RelationChain

/-! # 共尾 ω 树枝的实际相邻结点列

每一步取分支上严格较大的最小结点，以 ZF 的确定迭代构造内部 ω 列。
最小性保证相邻项确实是树前驱，因而不会跳过恢复图的一点扩张。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem It_pred_d.unique_l {ω T i j y : M.Domain} (order : It_order_d ω T)
    (h : It_pred_d T i y) (g : It_pred_d T j y) (hy : M.mem y ω) : i = j := by
  have ij := ((g.2 i).mp ((h.2 i).mpr (Or.inr (order.refl i (order.ordinal.transitive y hy i h.1))))).elim
    (fun eq => (KP.mem_irrefl_d (ZF.modelsKP hZF) y (eq ▸ h.1)).elim) id
  have ji := ((h.2 j).mp ((g.2 j).mpr (Or.inr (order.refl j (order.ordinal.transitive y hy j g.1))))).elim
    (fun eq => (KP.mem_irrefl_d (ZF.modelsKP hZF) y (eq ▸ g.1)).elim) id
  rcases order.forward i j ij with eq | lt
  · exact eq
  · rcases order.forward j i ji with eq | gt
    · exact eq.symm
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) i ((order.ordinal.mem (order.bound j i ji).2).transitive j gt i lt)).elim

theorem It_branch_d.successor_sequence_l {ω T B z : M.Domain} (hw : M.IsOmega ω)
    (order : It_order_d ω T) (branch : It_branch_d ω T B) (hz : M.mem z B) :
    ∃ F, Fn0_d ω B F ∧ (∀ e, (∀ x, ¬ M.mem x e) → Rd_entry_d e z F) ∧
      (∀ i j x y, M.SuccessorOf j i → Rd_entry_d i x F → Rd_entry_d j y F → It_pred_d T x y) ∧
      ∀ i x, Rd_entry_d i x F → z = x ∨ M.mem z x := by
  have ord := hw.isOrdinal hZF
  have next x (hx : M.mem x B) : ∃ y, M.mem y B ∧ M.mem x y := by
    obtain ⟨j, succ, hj⟩ := hw.1.2 x (branch.subset x hx)
    obtain ⟨y, hy, le⟩ := branch.cofinal j hj
    exact ⟨y, hy, le.elim (fun eq => eq ▸ succ.predecessor_mem)
      (fun h => (ord.mem (branch.subset y hy)).transitive j h x succ.predecessor_mem)⟩
  let ρ : Env M 1 := ⟨fun _ => B, fun _ => B⟩
  let φ : BinarySchema 1 := { body := set[3] ⟪⌜(.newest : Term 3)⌝ₛ ∈ ⌜(.bound 2 : Term 3)⌝ₛ ∧
    ⌜(.bound 1 : Term 3)⌝ₛ ∈ ⌜(.newest : Term 3)⌝ₛ ∧
    (∀ y ∈ ⌜(.bound 2 : Term 3)⌝ₛ, ⌜(.bound 1 : Term 3)⌝ₛ ∈ y → ⌜(.newest : Term 3)⌝ₛ ⊆ y)⟫ }
  have sat x y : φ.denote ρ x y ↔ M.mem y B ∧ M.mem x y ∧
      ∀ v, M.mem v B → M.mem x v → M.MemberSubset y v := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff]; rfl
  have least x (hx : M.mem x B) : ∃ y, φ.denote ρ x y := by
    let ψ : UnarySchema 1 := { body := .mem (.bound 1) .newest }
    let η : Env M 1 := ⟨fun _ => x, fun _ => x⟩
    obtain ⟨C, spec⟩ := ZF.separation_exists_d hZF ψ η B
    have read v : M.mem v C ↔ M.mem v B ∧ M.mem x v := spec v
    obtain ⟨y, hy, hxy⟩ := next x hx
    obtain ⟨v, hv, min⟩ := ord.wellOrder.least C (fun v h => branch.subset v ((read v).mp h).1)
      ⟨y, (read y).mpr ⟨hy, hxy⟩⟩
    refine ⟨v, (sat x v).mpr ⟨((read v).mp hv).1, ((read v).mp hv).2, fun w hw xw => ?_⟩⟩
    rcases min w ((read w).mpr ⟨hw, xw⟩) with eq | lt
    · exact fun a ha => (eq a).mp ha
    · exact (ord.mem (branch.subset w hw)).transitive v lt
  obtain ⟨G, gf, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ least (by
    intro x _ y v hy hv
    obtain ⟨hy, xy, ly⟩ := (sat x y).mp hy
    obtain ⟨hv, xv, lv⟩ := (sat x v).mp hv
    exact hZF.1.eq_of_same_members y v (fun a => ⟨ly v hv xv a, lv y hy xy a⟩))
    (fun x y _ h => ((sat x y).mp h).1)
  obtain ⟨F, ff, first, steps⟩ := ZFC.iterate_l I hZF hw gf hz
  have step i j x y (succ : M.SuccessorOf j i) (hx : Rd_entry_d i x F) (hy : Rd_entry_d j y F) :=
    (sat x y).mp ((gs x y).mp (steps i j x y succ hx hy)).2
  have pred i j x y (succ : M.SuccessorOf j i) (hx : Rd_entry_d i x F) (hy : Rd_entry_d j y F) : It_pred_d T x y := by
    obtain ⟨hyB, xy, least⟩ := step i j x y succ hx hy
    obtain ⟨l, _, yl⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF (branch.subset y hyB) ⟨x, xy⟩
    obtain ⟨k, pk⟩ := order.predecessor l y (branch.subset y hyB) yl
    have xyT := branch.forward_l order (ff.output_mem_of_pairMember hx) hyB (Or.inr xy)
    have xk := ((pk.2 x).mp xyT).elim (fun eq => (KP.mem_irrefl_d (ZF.modelsKP hZF) y (eq ▸ xy)).elim) id
    rcases order.forward x k xk with eq | xk
    · exact eq.symm ▸ pk
    · have ky := (pk.2 k).mpr (Or.inr (order.refl k (ord.transitive y (branch.subset y hyB) k pk.1)))
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) k (least k (branch.down k y ky hyB) xk k pk.1)).elim
  let η : Env M 0 := ⟨Fin.elim0, fun _ => F⟩
  let ψ : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  have inc := ZF.rel_chain_l I hZF ψ η hw ff
    (fun x y z _ _ hz xy yz => (ord.mem (branch.subset z hz)).transitive y yz x xy)
    (fun i j x y succ hx hy => (step i j x y succ hx hy).2.1)
  obtain ⟨e, empty, he⟩ := hw.1.1
  refine ⟨F, fn0_of_function_l (ZF.modelsKP hZF) ff, first, pred, fun i x hx => ?_⟩
  rcases ord.wellOrder.linear.compare e he i (ff.input_mem_of_pairMember hx) with eq | lt | gt
  · have eq := hZF.1.eq_of_same_members e i eq
    exact Or.inl (ff.1.2 i z x (eq ▸ first e empty) hx)
  · exact Or.inr (inc e i z x lt (first e empty) hx)
  · exact (empty i gt).elim

end YesMetaZFC.SetTheory.LargeCardinal
