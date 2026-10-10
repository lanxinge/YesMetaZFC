import YesMetaZFC.SetTheory.LargeCardinal.IterationCountable
import YesMetaZFC.SetTheory.LargeCardinal.IterationEnumeration

/-! # 原 ω 树的公共可数传递载体

实际收集所有模型的域并取并；每个域的可数性已由超幂和内部归纳证明。
对象选择只用于这一步可数并，之后的统一枚举仍用 ZF 的最小编号构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_countable_cover_l {ω c₀ T Q G E X₀ R₀ : M.Domain}
    (tree : It_tree_d hZF ω c₀ ω T Q G E) (mx : Smdl_d I c₀ X₀ R₀) (cx : M.CardinalLessOrEqual I X₀ ω) :
    ∃ Z ι, M.TransitiveSet Z ∧ M.IsSetInjectionFromTo I ι Z ω ∧
      ∀ i c X R, Rd_entry_d i c Q → KPair_d M c X R → M.MemberSubset X Z := by
  have count := it_countable_l hZF tree mx cx
  obtain ⟨D, fq⟩ := tree.diagram.family_l hZF
  let φ : BinarySchema 1 := { body := .existsE (.existsE (.conj
    (rd_entry0_m (.bound 3) (.bound 1) (.bound 4)) (kpair_m (.bound 1) (.bound 2) .newest))) }
  let ρ : Env M 1 := ⟨fun _ => Q, fun _ => Q⟩
  have sat i X : φ.denote ρ i X ↔ ∃ c R, Rd_entry_d i c Q ∧ KPair_d M c X R := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, kpair_sat_l M hZF.1]; rfl
  obtain ⟨U, us⟩ := ZF.exists_functionalImage hZF φ ρ ω (fun i hi => by
    obtain ⟨c, X, R, hc, mx⟩ := tree.diagram.model_l hZF hi
    exact ⟨X, (sat i X).mpr ⟨c, R, hc, mx.1⟩⟩) (fun i X Y hx hy => by
    obtain ⟨c, R, hc, mx⟩ := (sat i X).mp hx
    obtain ⟨d, S, hd, my⟩ := (sat i Y).mp hy
    exact (kpair_injective_l M mx ((tree.diagram.model_function.2 i d c hd hc) ▸ my)).1)
  obtain ⟨Z, hz⟩ := KP.exists_union (ZF.modelsKP hZF) U
  have sub i c X R (hc : Rd_entry_d i c Q) (hp : KPair_d M c X R) : M.MemberSubset X Z :=
    fun x hx => (hz x).mpr ⟨X, (us X).mpr ⟨i, (tree.diagram.model_domain i).mpr ⟨c, hc⟩, (sat i X).mpr ⟨c, R, hc, hp⟩⟩, hx⟩
  have trans : M.TransitiveSet Z := by
    intro x hx y hy
    obtain ⟨X, hX, hxX⟩ := (hz x).mp hx
    obtain ⟨i, _, hi⟩ := (us X).mp hX
    obtain ⟨c, R, hc, hp⟩ := (sat i X).mp hi
    obtain ⟨X', R', K, model, source⟩ := tree.sources i c hc
    obtain ⟨ex, er⟩ := kpair_injective_l M model.1.1 hp
    subst X' R'
    exact (hz y).mpr ⟨X, hX, source.transitive x hxX y hy⟩
  let ψ : BinarySchema 1 := { body := ep_at_m (.bound 2) (.bound 1) .newest }
  have psat i x : ψ.denote ρ i x ↔ Ep_at_d Q i x := ep_at_sat_l hZF.1 ..
  obtain ⟨id, hid⟩ := ZF.exists_identityBijection hZF I ω
  obtain ⟨ι, hι⟩ := ZFC.countable_cover_l I hZFC tree.omega ψ ρ ⟨id, hid.1⟩ (X := Z) (by
    intro i hi B bs
    obtain ⟨c, X, R, hc, mx⟩ := tree.diagram.model_l hZF hi
    have eq : B = X := hZF.1.eq_of_same_members B X (fun x => (bs x).trans
      ⟨fun h => (ep_at_read_l fq hc mx.1).mp ((psat i x).mp h.2),
        fun hx => ⟨sub i c X R hc mx.1 x hx, (psat i x).mpr ((ep_at_read_l fq hc mx.1).mpr hx)⟩⟩)
    exact eq.symm ▸ count i c X R hc mx.1) (by
    intro x hx
    obtain ⟨X, hX, hxX⟩ := (hz x).mp hx
    obtain ⟨i, hi, hs⟩ := (us X).mp hX
    obtain ⟨c, R, hc, hp⟩ := (sat i X).mp hs
    exact ⟨i, hi, (psat i x).mpr ⟨c, X, R, hc, hp, hxX⟩⟩)
  exact ⟨Z, ι, trans, hι, sub⟩

end YesMetaZFC.SetTheory.LargeCardinal
