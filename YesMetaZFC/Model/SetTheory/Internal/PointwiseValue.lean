import YesMetaZFC.Model.SetTheory.Internal.PointwiseAssignment

/-! # 代表函数赋值的实际逐点求值

逐坐标读取源内函数码，支撑外取固定基点。唯一值收集构造完整内部赋值，
因此逐点解释的语义关系确有赋值见证，且无需选择原子值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pe_value_exists_l (hZF : M.Models ZF) {ω b D X R E a p}
    (ext : Rf_ext_d I X R) (hE : M.IsFunctionSpace I E ω X) (ha : M.mem a E)
    (hb : M.MemberSubset b ω) (hp : M.mem p X) (hd : M.PairMember I p D R)
    (hh : ∀ i g, M.mem i b → M.PairMember I i g a → Rf_fun_d I X R D g) :
    ∃ f, M.mem f E ∧ Pe_assign_d I b D X R a f p := by
  classical
  let z := p
  have hz := hp
  let ρ : Env M 6 := ⟨Fin.cases b (Fin.cases p (Fin.cases a (Fin.cases z (Fin.cases X (fun _ => R))))), fun _ => z⟩
  let φ : BinarySchema 6 := {
    body := .disj
      (.conj (.mem (.bound 1) (.bound 2)) (.existsE (.conj
        (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 5)) (rf_val_m (𝒞 := 𝒞) (.bound 7) (.bound 8) (.bound 4) (.bound 1) .newest))))
      (.conj (.neg (.mem (.bound 1) (.bound 2))) (Formula.extensionalEq .newest (.bound 5))) }
  have sat i x : φ.denote ρ i x ↔
      (M.mem i b ∧ ∃ g, M.PairMember I i g a ∧ Rf_val_d I X R p x g) ∨ (¬ M.mem i b ∧ x = z) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I,
      rf_val_sat_l I, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  have hA := (hE a).mp ha
  obtain ⟨f, hf, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X)
    (fun i _ => by
      by_cases hi : M.mem i b
      · obtain ⟨g, _, hg⟩ := hA.2.2 i (hb i hi)
        obtain ⟨x, hx⟩ := (hh i g hi hg).value_l I ext hp hd
        exact ⟨x, (sat i x).mpr (Or.inl ⟨hi, g, hg, hx⟩)⟩
      · exact ⟨z, (sat i z).mpr (Or.inr ⟨hi, rfl⟩)⟩)
    (fun i _ x y hx hy => by
      rcases (sat i x).mp hx with ⟨hi, g, hg, hx⟩ | ⟨hi, rfl⟩ <;>
        rcases (sat i y).mp hy with ⟨hj, l, hl, hy⟩ | ⟨hj, rfl⟩
      · have eq := hA.1.2 i g l hg hl
        subst l
        exact (hh i g hi hg).unique_l I ext hx hy
      · exact (hj hi).elim
      · exact (hi hj).elim
      · rfl)
    (fun i x _ hx => by
      rcases (sat i x).mp hx with ⟨hi, g, hg, hx⟩ | ⟨_, rfl⟩
      · exact (hx.bounds_l I).2.1
      · exact hz)
  refine ⟨f, (hE f).mpr hf, fun i hi => ?_⟩
  obtain ⟨g, _, hg⟩ := hA.2.2 i (hb i hi)
  have hG := hh i g hi hg
  obtain ⟨x, hx⟩ := hG.value_l I ext hp hd
  exact ⟨g, x, hg, hG, hx, (spec i x).mpr ⟨hb i hi, (sat i x).mpr (Or.inl ⟨hi, g, hg, hx⟩)⟩⟩

end YesMetaZFC.SetTheory.Internal
