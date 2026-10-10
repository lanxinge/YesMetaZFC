import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Model
import YesMetaZFC.Model.SetTheory.Internal.PredicateEmbedding
import YesMetaZFC.SetTheory.DependentChoice

/-! # 实际代表图下降到商图

代表变换若精确保持几乎处处相等，其诱导商图由唯一值收集得到，并为单射。
所有输入都是既有集合图；后续源内坐标拉回直接实例化此构造。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_lift_d (K p q j : M.Domain) : Prop := ∀ f g B C,
  M.PairMember I f g K → M.PairMember I f B p → M.PairMember I g C q → M.PairMember I B C j

theorem rp_lift_exists_l (hZF : M.Models ZF) {D E X Y U V F G p q C N K}
    (hU : FilterZF.Base_d (ℳ := M) D U) (hV : FilterZF.Base_d (ℳ := M) E V)
    (hp : Rp_map_d I D X U F p C) (hq : Rp_map_d I E Y V G q N) (hK : M.IsSetFunctionFromTo I K F G)
    (he : ∀ f g f' g', M.PairMember I f f' K → M.PairMember I g g' K →
      (Rp_eq_d X U f g ↔ Rp_eq_d Y V f' g')) :
    ∃ j, M.IsSetInjectionFromTo I j C N ∧ Rp_lift_d I K p q j := by
  let ρ : Env M 5 := ⟨Fin.cases F (Fin.cases G (Fin.cases p (Fin.cases q (fun _ => K)))), fun _ => C⟩
  let φ : BinarySchema 5 := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 4)
      (.conj (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 3) (.bound 6))
        (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 8))
          (Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 7))))) }
  have sat B A : φ.denote ρ B A ↔ ∃ f, M.mem f F ∧ ∃ g, M.mem g G ∧
      M.PairMember I f B p ∧ M.PairMember I f g K ∧ M.PairMember I g A q := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  have equal B C A Z (hB : φ.denote ρ B A) (hC : φ.denote ρ C Z) : B = C ↔ A = Z := by
    obtain ⟨f, _, g, _, hfp, hfg, hgq⟩ := (sat B A).mp hB
    obtain ⟨f', _, g', _, hfp', hfg', hgq'⟩ := (sat C Z).mp hC
    exact (rp_kernel_l I hZF.1 hU hp hfp hfp').trans ((he f f' g g' hfg hfg').trans
      (rp_kernel_l I hZF.1 hV hq hgq hgq').symm)
  obtain ⟨j, hj, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := N)
    (fun B hB => by
      obtain ⟨f, hfp⟩ := (hp.range B).mp hB
      obtain ⟨g, hg, hfg⟩ := hK.2.2 f (hp.projection.input_mem_of_pairMember hfp)
      obtain ⟨A, _, hgq⟩ := hq.projection.2.2 g hg
      exact ⟨A, (sat B A).mpr ⟨f, hK.input_mem_of_pairMember hfg, g, hg, hfp, hfg, hgq⟩⟩)
    (fun B _ A Z hA hZ => (equal B B A Z hA hZ).mp rfl)
    (fun B A _ hA => ((sat B A).mp hA).elim fun _ hf => hf.2.elim fun _ hg => hq.projection.output_mem_of_pairMember hg.2.2.2)
  exact ⟨j, ⟨hj, fun B C A hB hC => (equal B C A A ((spec B A).mp hB).2 ((spec C A).mp hC).2).mpr rfl⟩,
    fun f g B A hfg hfp hgq => (spec B A).mpr ⟨hp.projection.output_mem_of_pairMember hfp,
      (sat B A).mpr ⟨f, hK.input_mem_of_pairMember hfg, g, hK.output_mem_of_pairMember hfg, hfp, hfg, hgq⟩⟩⟩

/-- 实际代表变换唯一确定商上的提升图。 -/
theorem rp_lift_unique_l (hE : Extensional M) {D E X Y U V F G p q C N K j k}
    (hp : Rp_map_d I D X U F p C) (hq : Rp_map_d I E Y V G q N) (hK : M.IsSetFunctionFromTo I K F G)
    (hj : M.IsSetFunctionFromTo I j C N) (hk : M.IsSetFunctionFromTo I k C N)
    (lj : Rp_lift_d I K p q j) (lk : Rp_lift_d I K p q k) : j = k := by
  have common B (hB : M.mem B C) : ∃ A, M.PairMember I B A j ∧ M.PairMember I B A k := by
    obtain ⟨f, hfp⟩ := (hp.range B).mp hB
    obtain ⟨g, hg, hfg⟩ := hK.2.2 f (hp.projection.input_mem_of_pairMember hfp)
    obtain ⟨A, _, hgq⟩ := hq.projection.2.2 g hg
    exact ⟨A, lj f g B A hfg hfp hgq, lk f g B A hfg hfp hgq⟩
  apply hj.1.1.eq_of_pairMember_iff hE hk.1.1
  intro B A
  constructor
  · intro ha
    obtain ⟨A', hbj, hbk⟩ := common B (hj.input_mem_of_pairMember ha)
    exact hj.1.2 B A' A hbj ha ▸ hbk
  · intro ha
    obtain ⟨A', hbj, hbk⟩ := common B (hk.input_mem_of_pairMember ha)
    exact hk.1.2 B A' A hbk ha ▸ hbj

/-- 对任意实际商赋值，原对象选择公理给出一张内部代表赋值图。 -/
theorem rp_representatives_l (hZFC : M.Models ZFC) {ω D X U F p C e}
    (hp : Rp_map_d I D X U F p C) (he : M.IsSetFunctionFromTo I e ω C) :
    ∃ a, M.IsSetFunctionFromTo I a ω F ∧ Smap_assign_d I ω p a e := by
  let ρ : Env M 2 := ⟨Fin.cases e (fun _ => p), fun _ => e⟩
  let φ : BinarySchema 2 := {
    body := .existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3))
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4))) }
  have sat i f : φ.denote ρ i f ↔ ∃ B, M.PairMember I i B e ∧ M.PairMember I f B p := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨a, ha, select⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := ω) (Y := F) (fun i hi => by
    obtain ⟨B, hB, hiB⟩ := he.2.2 i hi
    obtain ⟨f, hfB⟩ := (hp.range B).mp hB
    exact ⟨f, hp.projection.input_mem_of_pairMember hfB, (sat i f).mpr ⟨B, hiB, hfB⟩⟩)
  refine ⟨a, ha, fun i _ f B hif hfB => ?_⟩
  obtain ⟨C, hiC, hfC⟩ := (sat i f).mp (select i f hif)
  exact hp.projection.1.2 f C B hfC hfB ▸ hiC

end YesMetaZFC.SetTheory.Internal
