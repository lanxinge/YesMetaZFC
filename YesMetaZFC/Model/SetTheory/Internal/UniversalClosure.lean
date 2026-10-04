import YesMetaZFC.Model.SetTheory.Internal.UniversalSyntax
import YesMetaZFC.Model.SetTheory.Internal.Isomorphism

/-! # 非标准内部程序的全称闭包及理论的正向保持

在实际原公式上对 ω 归纳，逐坐标追加全称指令。量化到程序的坐标界后，
得到对所有赋值的有效性；因此初等嵌入的目标也满足源的全部内部理论。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sall_exists_l (hZF : M.Models ZF) {ω F n r b : M.Domain} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hb : M.mem b ω) : ∃ m G k, Sall_d I ω b F n r G m k := by
  let ρ := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push F).push n).push r
  let φ : UnarySchema 4 := {
    body := .existsE (.existsE (.existsE (sall_m (𝒞 := 𝒞) (.bound 7) (.bound 3)
      (.bound 6) (.bound 5) (.bound 4) (.bound 1) (.bound 2) .newest))) }
  have sat a : φ.denote ρ a ↔ ∃ m G k, Sall_d I ω a F n r G m k := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, sall_sat_l I hZF.1]; rfl
  apply (sat b).mp
  apply hω.induction (fun a => φ.denote ρ a) (ZF.separation_exists_d hZF φ ρ ω) ?_ ?_ b hb
  · intro z hz
    refine (sat z).mpr ⟨n, F, r, hF, hr, fun X R E f hE hf => ⟨?_, ?_⟩⟩
    · intro ht g hg tail
      have eq : f = g := ((hE f).mp hf).1.1.eq_of_pairMember_iff hZF.1 ((hE g).mp hg).1.1
        (fun i x => ⟨fun hx => (tail i (((hE f).mp hf).input_mem_of_pairMember hx) (hz i) x).mp hx,
          fun hx => (tail i (((hE g).mp hg).input_mem_of_pairMember hx) (hz i) x).mpr hx⟩)
      exact eq ▸ ht
    · exact fun ht => ht f hf (fun _ _ _ _ => Iff.rfl)
  · intro a ha ih s hs
    obtain ⟨m, G, k, hm, hk, old⟩ := (sat a).mp ih
    obtain ⟨l, H, t, build, code⟩ := sfm_all_l I hZF hω hm ha hk
    have successor i : M.mem i s ↔ M.mem i a ∨ i = a := (hs i).trans
      (or_congr Iff.rfl ⟨hZF.1.eq_of_same_members i a, fun eq => eq ▸ fun _ => Iff.rfl⟩)
    refine (sat s).mpr ⟨l, H, t, build.program, build.root, fun X R E f hE hf => ?_⟩
    rw [code X R E f hE hf]
    constructor
    · intro ht g hg tail
      obtain ⟨x, hx, hax⟩ := ((hE g).mp hg).2.2 a ha
      obtain ⟨u, hu, huf⟩ := senv_update_exists_l I hZF ((hE f).mp hf) ha hx
      apply (old X R E u hE ((hE u).mpr huf)).mp (ht x u hx hu) g hg
      intro i hi hn y
      classical
      by_cases eq : i = a
      · subst i
        exact (hu.2 a y).trans ⟨fun h => h.elim (fun h => h.2.symm ▸ hax) (fun h => (h.1 rfl).elim),
          fun h => Or.inl ⟨rfl, ((hE g).mp hg).1.2 a y x h hax⟩⟩
      · have hn' : ¬ M.mem i s := fun h => ((successor i).mp h).elim hn eq
        have update : M.PairMember I i y u ↔ M.PairMember I i y f := (hu.2 i y).trans
          ⟨fun h => h.elim (fun h => (eq h.1).elim) And.right, fun h => Or.inr ⟨eq, h⟩⟩
        exact update.trans (tail i hi hn' y)
    · intro ht x u hx hu
      apply (old X R E u hE ((hE u).mpr (hu.function_l I ((hE f).mp hf) ha hx))).mpr
      intro g hg tail
      apply ht g hg
      intro i hi hn y
      have hia : i ≠ a := fun eq => hn ((successor i).mpr (Or.inr eq))
      exact (⟨fun h => (hu.2 i y).mpr (Or.inr ⟨hia, h⟩),
        fun h => ((hu.2 i y).mp h).elim (fun h => (hia h.1).elim) And.right⟩ :
          M.PairMember I i y f ↔ M.PairMember I i y u).trans
        (tail i hi (fun h => hn ((successor i).mpr (Or.inl h))) y)

/-- 全称闭包的单点真值等价于原程序在全部内部赋值上的有效性。 -/
theorem sfm_close_l (hZF : M.Models ZF) {ω F n r : M.Domain} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) : ∃ m G k, Sfm_d I ω m G ∧ M.mem k m ∧
      ∀ X R E f, M.IsFunctionSpace I E ω X → M.mem f E →
        (Ssat_d I X R E G m k f ↔ ∀ g, M.mem g E → Ssat_d I X R E F n r g) := by
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF hω hF
  obtain ⟨m, G, k, hm, hk, code⟩ := sall_exists_l I hZF hω hF hr hb
  refine ⟨m, G, k, hm, hk, fun X R E f hE hf => (code X R E f hE hf).trans ⟨?_, ?_⟩⟩
  · intro ht g hg
    obtain ⟨h, hh, agree, tail⟩ := senv_patch_l I hZF ((hE f).mp hf) ((hE g).mp hg) (hω.transitive hZF b hb)
    exact (ssat_agree_l I hZF hF bound hE hr hg ((hE h).mpr hh) agree).mpr (ht h ((hE h).mpr hh) tail)
  · exact fun ht g hg _ => ht g hg

theorem Smap_d.valid_l (hZF : M.Models ZF) {ω c d X R Y S j F n r E K : M.Domain}
    (hω : M.IsOmega ω) (h : Smap_d I ω c d X Y j) (hc : Smdl_d I c X R) (hd : Smdl_d I d Y S)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hE : M.IsFunctionSpace I E ω X) (hK : M.IsFunctionSpace I K ω Y) :
    (∀ f, M.mem f E → Ssat_d I X R E F n r f) ↔ ∀ g, M.mem g K → Ssat_d I Y S K F n r g := by
  obtain ⟨x, hx⟩ := hc.2.1
  obtain ⟨f, hf, _⟩ := ZF.exists_constantFunction hZF I (source := ω) hx
  obtain ⟨g, hg, hfg⟩ := smap_assign_exists_l I hZF h.1.1 hf
  obtain ⟨m, G, k, hm, hk, code⟩ := sfm_close_l I hZF hω hF hr
  exact (code X R E f hE ((hE f).mpr hf)).symm.trans
    ((h.ssat_l I hZF.1 hc hd hm hk hE hK ((hE f).mpr hf) ((hK g).mpr hg) hfg).trans
      (code Y S K g hK ((hK g).mpr hg)))

theorem Smap_d.models_forward_l (hZF : M.Models ZF) {ω c d X R Y S j T}
    (hω : M.IsOmega ω) (h : Smap_d I ω c d X Y j) (hc : Smdl_d I c X R) (hd : Smdl_d I d Y S)
    (ht : Smodels_d I ω c T) : Smodels_d I ω d T := by
  obtain ⟨X', R', E, A, hc', hE, hA, sub, truth⟩ := ht
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I hc hc'
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω Y
  refine ⟨Y, S, K, A, hd, hK, hA, sub, fun a ha g hg => ?_⟩
  obtain ⟨n, F, r, code⟩ := (hA a).mp (sub a ha)
  apply (satisfies_decode_l I hZF.1 hd code hK).mpr
  exact (h.valid_l I hZF hω hc hd code.2.1 code.2.2 hE hK).mp
    (fun f hf => (satisfies_decode_l I hZF.1 hc' code hE).mp (truth a ha f hf)) g hg

end YesMetaZFC.SetTheory.Internal
