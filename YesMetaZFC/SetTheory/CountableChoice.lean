import YesMetaZFC.Model.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # DC 对实际可数关系的统一选择

把指标加入状态，直接调用内部 DC；第一坐标通过原公式归纳核验。
此接口仅选择对象模型中的 ω 族，不使用完整对象 AC 或宿主数据选择。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem dc_uniformize_l (hZF : M.Models ZF) {ω X R : M.Domain} (hω : M.IsOmega ω)
    (hDC : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω)
    (ht : ∀ i, M.mem i ω → ∃ x, M.mem x X ∧ Rd_entry_d i x R) :
    ∃ F, Fn0_d ω X F ∧ ∀ i x, Rd_entry_d i x F → Rd_entry_d i x R := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I ω X
  let φ : UnarySchema 1 := { body := .existsE (.existsE (.conj (kpair_m (.bound 2) (.bound 1) .newest)
    (rd_entry_m (.bound 1) .newest (.bound 3)))) }
  obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF φ ⟨fun _ => R, fun _ => R⟩ W
  have hD s : M.mem s D ↔ ∃ i, M.mem i ω ∧ ∃ x, M.mem x X ∧ KPair_d M s i x ∧ Rd_entry_d i x R := by
    have sat : φ.denote ⟨fun _ => R, fun _ => R⟩ s ↔ ∃ i x, KPair_d M s i x ∧ Rd_entry_d i x R := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        kpair_sat_l M hZF.1, rd_entry_sat_l hZF.1]; rfl
    refine (hd s).trans ((and_congr (hW s) sat).trans ⟨?_, ?_⟩)
    · rintro ⟨⟨i, hi, x, hx, hs⟩, j, y, hs', hjy⟩
      obtain ⟨rfl, rfl⟩ := I.injective hs hs'
      exact ⟨i, hi, x, hx, hs, hjy⟩
    · rintro ⟨i, hi, x, hx, hs, hix⟩
      exact ⟨⟨i, hi, x, hx, hs⟩, i, x, hs, hix⟩
  let ψ : BinarySchema 0 := { body := .existsE (.existsE (.existsE (.existsE (.conj
    (kpair_m (.bound 5) (.bound 3) (.bound 2)) (.conj (kpair_m (.bound 4) (.bound 1) .newest)
      (Formula.isSuccessor (.bound 1) (.bound 3))))))) }
  obtain ⟨S, _, hs⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ⟨Fin.elim0, fun _ => R⟩ D
  have step s t : Rd_entry_d s t S → ∃ i x j y, KPair_d M s i x ∧ KPair_d M t j y ∧ M.SuccessorOf j i := by
    intro hst
    have h := ((hs s t).mp hst).2.2
    simpa only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, Formula.satisfies_isSuccessor_iff] using! h
  obtain ⟨o, ho, hoω⟩ := hω.1.1
  obtain ⟨a, ha, hoa⟩ := ht o hoω
  obtain ⟨s, hsa⟩ := I.total o a
  obtain ⟨G, hG, hz, next⟩ := hDC D S s ((hD s).mpr ⟨o, hoω, a, ha, hsa, hoa⟩) (fun u hu => by
    obtain ⟨i, hi, x, _, hux, _⟩ := (hD u).mp hu
    obtain ⟨j, hji, hjω⟩ := hω.1.2 i hi
    obtain ⟨y, hy, hjy⟩ := ht j hjω
    obtain ⟨v, hv⟩ := I.total j y
    have hvD := (hD v).mpr ⟨j, hjω, y, hy, hv, hjy⟩
    refine ⟨v, hvD, (hs u v).mpr ⟨hu, hvD, ?_⟩⟩
    simpa only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, Formula.satisfies_isSuccessor_iff] using! ⟨i, x, j, y, hux, hv, hji⟩)
  have coords : ∀ i, M.mem i ω → ∀ s, Rd_entry_d i s G → ∃ x, KPair_d M s i x := by
    apply hω.induction (fun i => ∀ s, Rd_entry_d i s G → ∃ x, KPair_d M s i x)
    · let θ : UnarySchema 1 := { body := .forallE (.imp (rd_entry_m (.bound 1) .newest (.bound 2))
        (.existsE (kpair_m (.bound 1) (.bound 2) .newest))) }
      obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF θ ⟨fun _ => G, fun _ => G⟩ ω
      exact ⟨C, fun i => by simpa only [θ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
        Formula.satisfies_exists_iff, rd_entry_sat_l hZF.1, kpair_sat_l M hZF.1] using! hC i⟩
    · intro z he t hzt
      have ez := hZF.1.eq_of_same_members z o (fun x => iff_of_false (he x) (ho x))
      exact ⟨a, (hG.1.2 z t s hzt (hz z he)).symm ▸ ez.symm ▸ hsa⟩
    · intro i hi ih j hji t hjt
      obtain ⟨u, _, hiu⟩ := hG.2.2 i hi
      obtain ⟨x, hux⟩ := ih u hiu
      obtain ⟨i', x', j', y, hux', hty, hji'⟩ := step u t (next i j u t hji hiu hjt)
      obtain ⟨rfl, rfl⟩ := I.injective hux hux'
      exact ⟨y, Structure.SuccessorOf.eq hZF.1 hji' hji ▸ hty⟩
  let θ : BinarySchema 1 := { body := .existsE (.conj (rd_entry_m (.bound 2) .newest (.bound 3))
    (kpair_m .newest (.bound 2) (.bound 1))) }
  let ρ : Env M 1 := ⟨fun _ => G, fun _ => G⟩
  have sat i x : θ.denote ρ i x ↔ ∃ s, Rd_entry_d i s G ∧ KPair_d M s i x := by
    simp only [θ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1, kpair_sat_l M hZF.1]; rfl
  have val i x (hx : θ.denote ρ i x) : M.mem x X ∧ Rd_entry_d i x R := by
    obtain ⟨t, hit, htx⟩ := (sat i x).mp hx
    obtain ⟨j, _, y, hy, hty, hjy⟩ := (hD t).mp (hG.output_mem_of_pairMember hit)
    obtain ⟨rfl, rfl⟩ := I.injective htx hty
    exact ⟨hy, hjy⟩
  obtain ⟨F, hf, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I θ ρ (source := ω) (target := X)
    (fun i hi => by
      obtain ⟨s, _, his⟩ := hG.2.2 i hi
      obtain ⟨x, hs⟩ := coords i hi s his
      exact ⟨x, (sat i x).mpr ⟨s, his, hs⟩⟩)
    (fun i _ x y hx hy => by
      obtain ⟨s, his, hs⟩ := (sat i x).mp hx
      obtain ⟨t, hit, ht⟩ := (sat i y).mp hy
      exact (I.injective hs (hG.1.2 i t s hit his ▸ ht)).2)
    (fun i x _ hx => (val i x hx).1)
  exact ⟨F, fn0_of_function_l (ZF.modelsKP hZF) hf, fun i x hx => (val i x ((spec i x).mp hx).2).2⟩

theorem dc_uniformize_formula_l (hZF : M.Models ZF) {n} (φ : BinarySchema n) (ρ : Env M n)
    {ω X : M.Domain} (hω : M.IsOmega ω) (hDC : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω)
    (ht : ∀ i, M.mem i ω → ∃ x, M.mem x X ∧ φ.denote ρ i x) :
    ∃ F, Fn0_d ω X F ∧ ∀ i x, Rd_entry_d i x F → φ.denote ρ i x := by
  obtain ⟨W, hW⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) ω X
  obtain ⟨R, _, hr⟩ := ZF.exists_setRelationOn_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ W
  obtain ⟨F, hf, spec⟩ := dc_uniformize_l hZF hω hDC (fun i hi => (ht i hi).imp fun x hx =>
    ⟨hx.1, (hr i x).mpr ⟨(hW i).mpr (Or.inl hi), (hW x).mpr (Or.inr hx.1), hx.2⟩⟩)
  exact ⟨F, hf, fun i x hx => ((hr i x).mp (spec i x hx)).2.2⟩

end YesMetaZFC.SetTheory
