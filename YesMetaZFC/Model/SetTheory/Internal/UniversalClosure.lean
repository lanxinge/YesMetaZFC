import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Internal.Support
import YesMetaZFC.Model.SetTheory.Internal.Isomorphism

/-! # 全称闭包的内部赋值规格

量化坐标 b 以下的变量后，只固定其余坐标。全部条件均有实际原公式，
供对象 ω 上的归纳使用；b 不要求是外部标准自然数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Senv_tail_d (ω b f g : M.Domain) : Prop := ∀ i, M.mem i ω → ¬ M.mem i b →
  ∀ x, M.PairMember I i x f ↔ M.PairMember I i x g

def senv_tail_m {d} (ω b f g : Term d) : Formula 1 d := Formula.forallMem ω
  (.imp (.neg (.mem .newest b.weaken)) (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken)
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest g.weaken.weaken))))
derive_free_closed senv_tail_m

theorem senv_tail_sat_l {d} (ρ : Env M d) (ω b f g : Term d) :
    Formula.satisfies ρ (senv_tail_m (𝒞 := 𝒞) ω b f g) ↔
      Senv_tail_d I (ω.eval ρ) (b.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [senv_tail_m, Senv_tail_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

/-- 拼接两张真实赋值图：b 内取 g，b 外取 f。 -/
theorem senv_patch_l (hZF : M.Models ZF) {ω X b f g : M.Domain}
    (hf : M.IsSetFunctionFromTo I f ω X) (hg : M.IsSetFunctionFromTo I g ω X)
    (hb : M.MemberSubset b ω) : ∃ h, M.IsSetFunctionFromTo I h ω X ∧
      Senv_agree_d I b g h ∧ Senv_tail_d I ω b f h := by
  classical
  let ρ := ((⟨fun _ => b, fun _ => b⟩ : Env M 1).push f).push g
  let φ : BinarySchema 3 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 4)) (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2)))
      (.conj (.neg (.mem (.bound 1) (.bound 4))) (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))) }
  have sat i x : φ.denote ρ i x ↔ (M.mem i b ∧ M.PairMember I i x g) ∨ (¬ M.mem i b ∧ M.PairMember I i x f) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  obtain ⟨h, hh, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X)
    (fun i hi => by
      by_cases h : M.mem i b
      · obtain ⟨x, _, hx⟩ := hg.2.2 i hi
        exact ⟨x, (sat i x).mpr (Or.inl ⟨h, hx⟩)⟩
      · obtain ⟨x, _, hx⟩ := hf.2.2 i hi
        exact ⟨x, (sat i x).mpr (Or.inr ⟨h, hx⟩)⟩)
    (fun i _ x y hx hy => by
      rcases (sat i x).mp hx with ⟨hi, hx⟩ | ⟨hi, hx⟩ <;>
        rcases (sat i y).mp hy with ⟨hj, hy⟩ | ⟨hj, hy⟩
      · exact hg.1.2 i x y hx hy
      · exact (hj hi).elim
      · exact (hi hj).elim
      · exact hf.1.2 i x y hx hy)
    (fun i x _ hx => ((sat i x).mp hx).elim (fun h => hg.output_mem_of_pairMember h.2) (fun h => hf.output_mem_of_pairMember h.2))
  refine ⟨h, hh, fun i x hi => ?_, fun i hi hn x => ?_⟩
  · exact ⟨fun hx => (spec i x).mpr ⟨hb i hi, (sat i x).mpr (Or.inl ⟨hi, hx⟩)⟩,
      fun hx => ((sat i x).mp ((spec i x).mp hx).2).elim And.right (fun h => (h.1 hi).elim)⟩
  · exact ⟨fun hx => (spec i x).mpr ⟨hi, (sat i x).mpr (Or.inr ⟨hn, hx⟩)⟩,
      fun hx => ((sat i x).mp ((spec i x).mp hx).2).elim (fun h => (hn h.1).elim) And.right⟩

def Sall_d (ω b F n r G m k : M.Domain) : Prop := Sfm_d I ω m G ∧ M.mem k m ∧
  ∀ X R E f, M.IsFunctionSpace I E ω X → M.mem f E →
    (Ssat_d I X R E G m k f ↔ ∀ g, M.mem g E → Senv_tail_d I ω b f g → Ssat_d I X R E F n r g)

def sall_m {d} (ω b F n r G m k : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken
  .conj (sfm_m (𝒞 := 𝒞) ω m G) (.conj (.mem k m) (.forallE (.forallE (.forallE (.forallE
    (.imp (Formula.isFunctionSpace 𝒞 (.bound 1) (w ω) (.bound 3)) (.imp (.mem .newest (.bound 1))
      (.iff (ssat_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) (w G) (w m) (w k) .newest)
        (Formula.forallMem (.bound 1) (.imp
          (senv_tail_m (𝒞 := 𝒞) (w ω).weaken (w b).weaken (.bound 1) .newest)
          (ssat_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (w F).weaken (w n).weaken (w r).weaken .newest)))))))))))
@[simp] theorem sall_closed_l {d} (ω b F n r G m k : Term d)
    (hω : ω.freeSupport = []) (hb : b.freeSupport = []) (hF : F.freeSupport = []) (hn : n.freeSupport = [])
    (hr : r.freeSupport = []) (hG : G.freeSupport = []) (hm : m.freeSupport = []) (hk : k.freeSupport = []) :
    (sall_m (𝒞 := 𝒞) ω b F n r G m k).FreeClosed := by
  simp -implicitDefEqProofs [sall_m, Definitional.Formula.FreeClosed, Formula.isFunctionSpace,
    hω, hb, hF, hn, hr, hG, hm, hk]

theorem sall_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω b F n r G m k : Term d) :
    Formula.satisfies ρ (sall_m (𝒞 := 𝒞) ω b F n r G m k) ↔
      Sall_d I (ω.eval ρ) (b.eval ρ) (F.eval ρ) (n.eval ρ) (r.eval ρ) (G.eval ρ) (m.eval ρ) (k.eval ρ) := by
  simp only [sall_m, Sall_d, Formula.satisfies_conj_iff, sfm_sat_l I hE, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_isFunctionSpace_iff I hE,
    Formula.satisfies_iff_iff, ssat_sat_l I hE, Formula.satisfies_forallMem_iff, senv_tail_sat_l I,
    Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 非标准内部程序的全称闭包及理论的正向保持

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
    obtain ⟨h, hh, agree, tail⟩ := senv_patch_l I hZF ((hE f).mp hf) ((hE g).mp hg) (hω.transitive (ZF.modelsKP hZF) b hb)
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
