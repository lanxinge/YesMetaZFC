import YesMetaZFC.SetTheory.Filter.Relative
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition
import YesMetaZFC.Model.SetTheory.Internal.Quotient
import YesMetaZFC.SetTheory.Ord.Arithmetic.Recursion
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.Card.FiniteSequenceLift
import YesMetaZFC.Model.SetTheory.Internal.Theory
import YesMetaZFC.SetTheory.Filter.Projection
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.Model.SetTheory.Relations.Ultrafilter
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Graph
import YesMetaZFC.Model.SetTheory.Source.Relation
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial

/-! # 内部约化幂的几乎处处关系

代表元都是模型内函数图。等同和关系由一个实际滤子成员上的逐点见证定义；
有限交共同细化直接给出等价性和关系对代表元替换的不变性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_eq_d (Q U f g : M.Domain) : Prop := ∃ A, M.mem A U ∧ ∀ i, M.mem i A →
  ∃ x, M.mem x Q ∧ Rd_entry_d i x f ∧ Rd_entry_d i x g

def rp_eq_m {d} (Q U f g : Term d) : Formula 1 d := Formula.existsMem U (Formula.forallMem .newest
  (Formula.existsMem Q.weaken.weaken (.conj (rd_entry0_m (.bound 1) .newest f.weaken.weaken.weaken)
    (rd_entry0_m (.bound 1) .newest g.weaken.weaken.weaken))))
derive_free_closed rp_eq_m

theorem rp_eq_delta_l {d} (Q U f g : Term d) : (rp_eq_m Q U f g).IsDelta0 :=
  .existsMem _ (.forallMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))

theorem rp_eq_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Q U f g : Term d) :
    Formula.satisfies ρ (rp_eq_m Q U f g) ↔ Rp_eq_d (Q.eval ρ) (U.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [rp_eq_m, Rp_eq_d, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_conj_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem rp_eq_refl_l {D Q U f} (hU : FilterZF.Base_d (ℳ := M) D U) (hf : Fn0_d D Q f) : Rp_eq_d Q U f f :=
  ⟨D, hU.top, fun i hi => (hf.2.1 i hi).imp fun _ hx => ⟨hx.1, hx.2, hx.2⟩⟩

theorem rp_eq_member_l {D Q P U f g A} (hU : FilterZF.Rel_ultra_d (ℳ := M) D P U)
    (hA : M.mem A P) (hs : ∀ v, M.mem v A ↔ M.mem v D ∧
      ∃ x, M.mem x Q ∧ Rd_entry_d v x f ∧ Rd_entry_d v x g) : M.mem A U ↔ Rp_eq_d Q U f g := by
  refine ⟨fun h => ⟨A, h, fun v hv => ((hs v).mp hv).2⟩, ?_⟩
  rintro ⟨B, hB, hb⟩
  exact hU.upward B A hB hA (fun v hv => (hs v).mpr ⟨hU.base.bounds B hB v hv, hb v hv⟩)

theorem Rp_eq_d.symm_l {Q U f g : M.Domain} (h : Rp_eq_d Q U f g) : Rp_eq_d Q U g f :=
  h.imp fun _ ha => ⟨ha.1, fun i hi => (ha.2 i hi).imp fun _ hx => ⟨hx.1, hx.2.symm⟩⟩

theorem Rp_eq_d.trans_l {D Q U f g h} (hU : FilterZF.Base_d (ℳ := M) D U) (hg : Fn0_d D Q g)
    (hfg : Rp_eq_d Q U f g) (hgh : Rp_eq_d Q U g h) : Rp_eq_d Q U f h := by
  obtain ⟨A, hAU, hA⟩ := hfg
  obtain ⟨B, hBU, hB⟩ := hgh
  obtain ⟨C, hCU, hCA, hCB⟩ := hU.meet A B hAU hBU
  refine ⟨C, hCU, fun i hi => ?_⟩
  obtain ⟨x, hx, hxf, hxg⟩ := hA i (hCA i hi)
  obtain ⟨y, hy, hyg, hyh⟩ := hB i (hCB i hi)
  have eq := hg.2.2 i (hg.bound_l hxg).1 y hy x hx hyg hxg
  exact ⟨x, hx, hxf, eq ▸ hyh⟩

def Rp_rel_d (Q U R f g : M.Domain) : Prop := ∃ A, M.mem A U ∧ ∀ i, M.mem i A →
  ∃ x, M.mem x Q ∧ ∃ y, M.mem y Q ∧ Rd_entry_d i x f ∧ Rd_entry_d i y g ∧ M.PairMember I x y R

def rp_rel_m {d} (Q U R f g : Term d) : Formula 1 d := Formula.existsMem U (Formula.forallMem .newest
  (Formula.existsMem Q.weaken.weaken (Formula.existsMem Q.weaken.weaken.weaken (.conj
    (rd_entry0_m (.bound 2) (.bound 1) f.weaken.weaken.weaken.weaken) (.conj
      (rd_entry0_m (.bound 2) .newest g.weaken.weaken.weaken.weaken)
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken.weaken.weaken))))))
derive_free_closed rp_rel_m

theorem rp_rel_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Q U R f g : Term d) :
    Formula.satisfies ρ (rp_rel_m (𝒞 := 𝒞) Q U R f g) ↔
      Rp_rel_d I (Q.eval ρ) (U.eval ρ) (R.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [rp_rel_m, Rp_rel_d, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_conj_iff, rd_entry0_sat_l hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem rp_rel_transport_l {D Q U R f g f' g'} (hU : FilterZF.Base_d (ℳ := M) D U)
    (hf : Fn0_d D Q f) (hg : Fn0_d D Q g) (he : Rp_eq_d Q U f f') (hk : Rp_eq_d Q U g g')
    (h : Rp_rel_d I Q U R f g) : Rp_rel_d I Q U R f' g' := by
  obtain ⟨A, hAU, hA⟩ := he
  obtain ⟨B, hBU, hB⟩ := h
  obtain ⟨C, hCU, hC⟩ := hk
  obtain ⟨E, hEU, hEA, hEB⟩ := hU.meet A B hAU hBU
  obtain ⟨T, hTU, hTE, hTC⟩ := hU.meet E C hEU hCU
  refine ⟨T, hTU, fun i hi => ?_⟩
  obtain ⟨x, hx, hxf, hxf'⟩ := hA i (hEA i (hTE i hi))
  obtain ⟨y, hy, z, hz, hyf, hzg, hyz⟩ := hB i (hEB i (hTE i hi))
  obtain ⟨w, hw, hwg, hwg'⟩ := hC i (hTC i hi)
  have ey := hf.2.2 i (hf.bound_l hxf).1 y hy x hx hyf hxf
  have ez := hg.2.2 i (hg.bound_l hwg).1 z hz w hw hzg hwg
  exact ⟨x, hx, w, hw, hxf', hwg', ey ▸ ez ▸ hyz⟩

theorem rp_rel_congr_l {D Q U R f g f' g'} (hU : FilterZF.Base_d (ℳ := M) D U)
    (hf : Fn0_d D Q f) (hg : Fn0_d D Q g) (hf' : Fn0_d D Q f') (hg' : Fn0_d D Q g')
    (he : Rp_eq_d Q U f f') (hk : Rp_eq_d Q U g g') : Rp_rel_d I Q U R f g ↔ Rp_rel_d I Q U R f' g' :=
  ⟨rp_rel_transport_l I hU hf hg he hk, rp_rel_transport_l I hU hf' hg' he.symm_l hk.symm_l⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 模型内的函数等价类集合与投影

每个类由指定函数族上的分离得到，全部类由内部函数图的值域收集。
投影的核恰好是几乎处处相等，无须选择各类的代表元。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_class_d (Q U G f B : M.Domain) : Prop := ∀ g, M.mem g B ↔ M.mem g G ∧ Rp_eq_d Q U f g

def rp_class_m {d} (Q U G f B : Term d) : Formula 1 d := .forallE (.iff (.mem .newest B.weaken)
  (.conj (.mem .newest G.weaken) (rp_eq_m Q.weaken U.weaken f.weaken .newest)))
derive_free_closed rp_class_m

theorem rp_class_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Q U G f B : Term d) :
    Formula.satisfies ρ (rp_class_m Q U G f B) ↔
      Rp_class_d (Q.eval ρ) (U.eval ρ) (G.eval ρ) (f.eval ρ) (B.eval ρ) := by
  simp only [rp_class_m, Rp_class_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, rp_eq_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem rp_class_exists_l (hZF : M.Models ZF) (Q U G f : M.Domain) : ∃ B, Rp_class_d Q U G f B := by
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases U (fun _ => Q)), fun _ => Q⟩
  let φ : UnarySchema 3 := { body := rp_eq_m (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨B, hB⟩ := ZF.separation_exists_d hZF φ ρ G
  exact ⟨B, fun g => (hB g).trans (and_congr_right fun _ => rp_eq_sat_l hZF.1 _ _ _ _ _)⟩

theorem rp_class_eq_l (hE : Extensional M) {D Q U G f g B C}
    (hU : FilterZF.Base_d (ℳ := M) D U) (hG : ∀ f, M.mem f G → Fn0_d D Q f)
    (hf : M.mem f G) (hg : M.mem g G) (hB : Rp_class_d Q U G f B) (hC : Rp_class_d Q U G g C) :
    B = C ↔ Rp_eq_d Q U f g := by
  constructor
  · intro he
    have hfB := (hB f).mpr ⟨hf, rp_eq_refl_l hU (hG f hf)⟩
    exact ((hC f).mp (he ▸ hfB)).2.symm_l
  · intro he
    apply hE.eq_of_same_members B C
    intro v
    exact (hB v).trans ((and_congr_right fun _ =>
      ⟨fun hv => he.symm_l.trans_l hU (hG f hf) hv,
        fun hv => he.trans_l hU (hG g hg) hv⟩).trans (hC v).symm)

/-- 从实际候选集合中分离合法代表；候选可取源模型自身，而不要求全部背景函数。 -/
theorem rp_family_exists_l (hKP : M.Models KP) (D Q B : M.Domain) :
    ∃ G, ∀ f, M.mem f G ↔ M.mem f B ∧ Fn0_d D Q f := by
  let ρ : Env M 2 := ⟨Fin.cases Q (fun _ => D), fun _ => D⟩
  let φ : Delta0UnarySchema 2 := { body := fn0_m (.bound 2) (.bound 1) .newest, delta0 := fn0_delta_l .. }
  obtain ⟨G, hG⟩ := KP.separation_exists_d hKP φ ρ B
  exact ⟨G, fun f => (hG f).trans (and_congr_right fun _ => fn0_sat_l hKP.1 _ _ _ _)⟩

structure Rp_map_d (D Q U G p C : M.Domain) : Prop where
  functions : ∀ f, M.mem f G → Fn0_d D Q f
  projection : M.IsSetFunctionFromTo I p G C
  range : M.IsRangeOf I C p
  classes : ∀ f B, M.PairMember I f B p ↔ M.mem f G ∧ Rp_class_d Q U G f B

def rp_map_m {d} (D Q U G p C : Term d) : Formula 1 d := .conj
  (.forallE (.imp (.mem .newest G.weaken) (fn0_m D.weaken Q.weaken .newest))) (.conj
    (Formula.isFunctionFromTo 𝒞 p G C) (.conj (Formula.isRange 𝒞 C p) (.forallE (.forallE (.iff
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest p.weaken.weaken) (.conj (.mem (.bound 1) G.weaken.weaken)
        (rp_class_m Q.weaken.weaken U.weaken.weaken G.weaken.weaken (.bound 1) .newest)))))))
derive_free_closed rp_map_m

theorem rp_map_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D Q U G p C : Term d) :
    Formula.satisfies ρ (rp_map_m (𝒞 := 𝒞) D Q U G p C) ↔
      Rp_map_d I (D.eval ρ) (Q.eval ρ) (U.eval ρ) (G.eval ρ) (p.eval ρ) (C.eval ρ) := by
  simp only [rp_map_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, fn0_sat_l hE,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_isRange_iff I,
    Formula.satisfies_orderedPairMem_iff I, rp_class_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.functions, h.projection, h.range, h.classes⟩⟩

theorem rp_map_exists_l (hZF : M.Models ZF) {D Q U G}
    (hG : ∀ f, M.mem f G → Fn0_d D Q f) : ∃ p C, Rp_map_d I D Q U G p C := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF G
  let ρ : Env M 3 := ⟨Fin.cases G (Fin.cases U (fun _ => Q)), fun _ => Q⟩
  let φ : BinarySchema 3 := { body := rp_class_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat f B : φ.denote ρ f B ↔ Rp_class_d Q U G f B := rp_class_sat_l hZF.1 _ _ _ _ _ _
  obtain ⟨p, hp, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := G) (target := P)
    (fun f _ => (rp_class_exists_l hZF Q U G f).imp fun B hB => (sat f B).mpr hB)
    (fun f _ B C hB hC => hZF.1.eq_of_same_members B C (fun g => ((sat f B).mp hB g).trans ((sat f C).mp hC g).symm))
    (fun f B _ hB => (hP B).mpr fun g hg => (((sat f B).mp hB g).mp hg).1)
  obtain ⟨C, hC⟩ := ZF.exists_range_of_setFunction hZF I hp.1 hp.2.1
  exact ⟨p, C, ⟨hG, ⟨hp.1, hp.2.1, fun f hf => (hp.2.2 f hf).imp fun B hB =>
    ⟨(hC B).mpr ⟨f, hB.2⟩, hB.2⟩⟩, hC, fun f B => (spec f B).trans (and_congr_right fun _ => sat f B)⟩⟩

theorem rp_kernel_l (hE : Extensional M) {D Q U G p C f g B E}
    (hU : FilterZF.Base_d (ℳ := M) D U) (hp : Rp_map_d I D Q U G p C)
    (hf : M.PairMember I f B p) (hg : M.PairMember I g E p) : B = E ↔ Rp_eq_d Q U f g := by
  obtain ⟨hfG, hB⟩ := (hp.classes f B).mp hf
  obtain ⟨hgG, hE'⟩ := (hp.classes g E).mp hg
  exact rp_class_eq_l hE hU hp.functions hfG hgG hB hE'

theorem Rp_map_d.representative_l {D X U G p C f B} (hU : FilterZF.Base_d (ℳ := M) D U)
    (h : Rp_map_d I D X U G p C) (hf : M.PairMember I f B p) : M.mem f B := by
  obtain ⟨hfG, hB⟩ := (h.classes f B).mp hf
  exact (hB f).mpr ⟨hfG, rp_eq_refl_l hU (h.functions f hfG)⟩

/-- 类成员属于原代表族；这一步尚不需要滤基性质。 -/
theorem Rp_map_d.member_family_l {D X U G p C f B} (h : Rp_map_d I D X U G p C)
    (hB : M.mem B C) (hf : M.mem f B) : M.mem f G := by
  obtain ⟨g, hg⟩ := (h.range B).mp hB
  exact (((h.classes g B).mp hg).2 f |>.mp hf).1

/-- 类成员对应同一个实际商投影值。 -/
theorem Rp_map_d.member_l (hE : Extensional M) {D X U G p C f B}
    (hU : FilterZF.Base_d (ℳ := M) D U) (h : Rp_map_d I D X U G p C)
    (hB : M.mem B C) (hf : M.mem f B) : M.PairMember I f B p := by
  obtain ⟨g, hg⟩ := (h.range B).mp hB
  obtain ⟨hfG, hgf⟩ := ((h.classes g B).mp hg).2 f |>.mp hf
  obtain ⟨E, _, he⟩ := h.projection.2.2 f hfG
  exact ((rp_kernel_l I hE hU h hg he).mpr hgf).symm ▸ he

end YesMetaZFC.SetTheory.Internal

/-! ## 约化幂的实际内部结构码

在全部等价类组成的集合上分离商关系，并证明它可用任意代表元读取。
源关系与函数值域可以位于任意秩，不要求派生测度的原嵌入作用于这些函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Rp_model_d (D Q U R c G p C T : M.Domain) : Prop where
  map : Rp_map_d I D Q U G p C
  code : Smdl_d I c C T
  relation : ∀ f g B E, M.PairMember I f B p → M.PairMember I g E p →
    (M.PairMember I B E T ↔ Rp_rel_d I Q U R f g)

def rp_model_m {d} (D Q U R c G p C T : Term d) : Formula 1 d := .conj (rp_map_m (𝒞 := 𝒞) D Q U G p C)
  (.conj (smdl_m (𝒞 := 𝒞) c C T) (.forallE (.forallE (.forallE (.forallE
    (.imp (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) p.weaken.weaken.weaken.weaken)
      (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest p.weaken.weaken.weaken.weaken)
        (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest T.weaken.weaken.weaken.weaken)
          (rp_rel_m (𝒞 := 𝒞) Q.weaken.weaken.weaken.weaken U.weaken.weaken.weaken.weaken
            R.weaken.weaken.weaken.weaken (.bound 3) (.bound 2))))))))))
derive_free_closed rp_model_m

theorem rp_model_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D Q U R c G p C T : Term d) :
    Formula.satisfies ρ (rp_model_m (𝒞 := 𝒞) D Q U R c G p C T) ↔
      Rp_model_d I (D.eval ρ) (Q.eval ρ) (U.eval ρ) (R.eval ρ) (c.eval ρ) (G.eval ρ) (p.eval ρ) (C.eval ρ) (T.eval ρ) := by
  simp only [rp_model_m, Formula.satisfies_conj_iff, rp_map_sat_l I hE, smdl_sat_l I,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_iff_iff, rp_rel_sat_l I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.map, h.code, h.relation⟩⟩

theorem rp_model_exists_l (hZF : M.Models ZF) {D Q U G} (hU : FilterZF.Base_d (ℳ := M) D U)
    (hG : ∀ f, M.mem f G → Fn0_d D Q f) (h : ∃ f, M.mem f G) (R : M.Domain) :
    ∃ c p C T, Rp_model_d I D Q U R c G p C T := by
  obtain ⟨p, C, hp⟩ := rp_map_exists_l I hZF hG
  obtain ⟨f, hfG⟩ := h
  obtain ⟨B, hBC, _⟩ := hp.projection.2.2 f hfG
  let ρ : Env M 5 := ⟨Fin.cases p (Fin.cases G (Fin.cases Q (Fin.cases U (fun _ => R)))), fun _ => Q⟩
  let φ : BinarySchema 5 := { body := Formula.existsMem (.bound 3) (Formula.existsMem (.bound 4)
    (.conj (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 3) (.bound 4)) (.conj
      (Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 4))
      (rp_rel_m (𝒞 := 𝒞) (.bound 6) (.bound 7) (.bound 8) (.bound 1) .newest)))) }
  have sat B E : φ.denote ρ B E ↔ ∃ f, M.mem f G ∧ ∃ g, M.mem g G ∧
      M.PairMember I f B p ∧ M.PairMember I g E p ∧ Rp_rel_d I Q U R f g := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, rp_rel_sat_l I hZF.1]
    rfl
  obtain ⟨c, T, hc, ht⟩ := smdl_exists_l I hZF φ ρ ⟨B, hBC⟩
  refine ⟨c, p, C, T, ⟨hp, hc, fun f g B E hf hg => (ht B E).trans ?_⟩⟩
  rw [sat B E]
  constructor
  · rintro ⟨_, _, f', hfG, g', hgG, hf', hg', hfg⟩
    exact rp_rel_transport_l I hU (hp.functions f' hfG) (hp.functions g' hgG)
      ((rp_kernel_l I hZF.1 hU hp hf' hf).mp rfl) ((rp_kernel_l I hZF.1 hU hp hg' hg).mp rfl) hfg
  · intro hfg
    exact ⟨hp.projection.output_mem_of_pairMember hf, hp.projection.output_mem_of_pairMember hg,
      f, hp.projection.input_mem_of_pairMember hf, g, hp.projection.input_mem_of_pairMember hg, hf, hg, hfg⟩

/-- 指定候选函数集合后，实际分离全部合法代表并形成商结构。 -/
theorem rp_family_model_l (hZF : M.Models ZF) {D Q U B f} (hU : FilterZF.Base_d (ℳ := M) D U)
    (hfB : M.mem f B) (hf : Fn0_d D Q f) (R : M.Domain) : ∃ G c p C T,
      (∀ g, M.mem g G ↔ M.mem g B ∧ Fn0_d D Q g) ∧ Rp_model_d I D Q U R c G p C T := by
  obtain ⟨G, hG⟩ := rp_family_exists_l (ZF.modelsKP hZF) D Q B
  obtain ⟨c, p, C, T, h⟩ := rp_model_exists_l I hZF hU (fun g hg => ((hG g).mp hg).2)
    ⟨f, (hG f).mpr ⟨hfB, hf⟩⟩ R
  exact ⟨G, c, p, C, T, hG, h⟩

/-- 同一实际代表族决定唯一的类、投影和结构码。 -/
theorem Rp_model_d.unique_l (hE : Extensional M) {D Q U R G c p C T d q N S : M.Domain}
    (h : Rp_model_d I D Q U R c G p C T) (g : Rp_model_d I D Q U R d G q N S) : c = d := by
  have ep := g.map.projection.1.1.eq_of_pairMember_iff hE h.map.projection.1.1
    (fun f B => (g.map.classes f B).trans (h.map.classes f B).symm)
  subst q
  have ec := hE.eq_of_same_members N C (fun B => (g.map.range B).trans (h.map.range B).symm)
  subst N
  have et : S = T := by
    apply g.code.2.2.1.eq_of_pairMember_iff hE h.code.2.2.1
    intro B E
    have read {a b V W} (m : Rp_model_d I D Q U R a G p C V) (n : Rp_model_d I D Q U R b G p C W)
        (edge : M.PairMember I B E V) : M.PairMember I B E W := by
      obtain ⟨f, hf⟩ := (m.map.range B).mp (m.code.2.2.2 B E edge).1
      obtain ⟨g, hg⟩ := (m.map.range E).mp (m.code.2.2.2 B E edge).2
      exact (n.relation f g B E hf hg).mpr ((m.relation f g B E hf hg).mp edge)
    exact ⟨read g h, read h g⟩
  subst S
  exact I.unique h.code.1 g.code.1

end YesMetaZFC.SetTheory.Internal

/-! ## 实际代表图下降到商图

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

/-- 只提升给定内部有限坐标界，界外使用一个实际代表；无需可数选择。 -/
theorem rp_finite_representatives_l (hZF : M.Models ZF) {ω b D X U F p C e}
    (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hp : Rp_map_d I D X U F p C) (he : M.IsSetFunctionFromTo I e ω C) :
    ∃ a, M.IsSetFunctionFromTo I a ω F ∧ Smap_assign_d I b p a e := by
  have bω := hω.transitive (ZF.modelsKP hZF) b hb
  obtain ⟨o, _, ho⟩ := hω.1.1
  obtain ⟨B, hB, _⟩ := he.2.2 o ho
  obtain ⟨g, hg⟩ := (hp.range B).mp hB
  obtain ⟨s, hs⟩ := ZF.exists_restriction hZF I e b
  obtain ⟨t, ht, comm⟩ := ZF.fseq_lift_l I hZF hω
    (fun B hB => ((hp.range B).mp hB).imp fun f hf =>
      ⟨hp.projection.input_mem_of_pairMember hf, hf⟩) hb (hs.isSetFunctionFromTo he bω)
  obtain ⟨a, fill, ha⟩ := senv_fill_exists_l I hZF (ω := ω) ht (hp.projection.input_mem_of_pairMember hg)
  refine ⟨a, ha, fun i hi f B hif hfB => ?_⟩
  have hit : M.PairMember I i f t := by
    rcases ((fill.2 i f).mp hif).2 with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact (h hi).elim
  obtain ⟨C, _, hiC⟩ := he.2.2 i (bω i hi)
  exact hp.projection.1.2 f C B (comm i f C hit ((hs.2 i C).mpr ⟨hi, hiC⟩)) hfB ▸ hiC

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

/-! ## 完整测度在任意源代表族上的原子投影

代表族可以仅包含源内部函数。背景分离形成精确原子真值集，测度投影直接
给出等价及关系的保持、反映；不把整个背景函数空间替换进源超幂。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_atom_d (b : Bool) (X R f g v : M.Domain) : Prop := ∃ x, M.mem x X ∧ ∃ y, M.mem y X ∧
  Rd_entry_d v x f ∧ Rd_entry_d v y g ∧ (if b then x = y else M.PairMember I x y R)

def rp_atom_m (b : Bool) {d} (X R f g v : Term d) : Formula 1 d := Formula.existsMem X
  (Formula.existsMem X.weaken (.conj (rd_entry_m v.weaken.weaken (.bound 1) f.weaken.weaken)
    (.conj (rd_entry_m v.weaken.weaken .newest g.weaken.weaken)
      (if b then Formula.extensionalEq (.bound 1) .newest else Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken))))
@[simp] theorem rp_atom_closed_l (b : Bool) {d} (X R f g v : Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hf : f.freeSupport = [])
    (hg : g.freeSupport = []) (hv : v.freeSupport = []) : (rp_atom_m (𝒞 := 𝒞) b X R f g v).FreeClosed := by
  cases b <;> simp -implicitDefEqProofs [rp_atom_m, Definitional.Formula.FreeClosed, hX, hR, hf, hg, hv]

theorem rp_atom_sat_l (hE : Extensional M) (b : Bool) {d} (ρ : Env M d) (X R f g v : Term d) :
    Formula.satisfies ρ (rp_atom_m (𝒞 := 𝒞) b X R f g v) ↔
      Rp_atom_d I b (X.eval ρ) (R.eval ρ) (f.eval ρ) (g.eval ρ) (v.eval ρ) := by
  cases b <;> simp only [rp_atom_m, Rp_atom_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_orderedPairMem_iff I,
    Bool.false_eq_true, ↓reduceIte, Definitional.Term.eval_weaken] <;> rfl

theorem rp_atom_eq_l {X U R f g : M.Domain} :
    (∃ A, M.mem A U ∧ ∀ v, M.mem v A → Rp_atom_d I true X R f g v) ↔ Rp_eq_d X U f g := by
  refine exists_congr fun A => and_congr_right fun _ => forall_congr' fun v => imp_congr_right fun _ => ?_
  exact ⟨fun ⟨x, hx, y, _, hfx, hgy, e⟩ => ⟨x, hx, hfx, e.symm ▸ hgy⟩,
    fun ⟨x, hx, hfx, hgx⟩ => ⟨x, hx, x, hx, hfx, hgx, rfl⟩⟩

theorem rp_pull_atom_l (hZF : M.Models ZF) (b : Bool) {D E X R P Q U V t f g f' g' : M.Domain}
    (hP : M.IsPowerSetOf P D) (hU : Rel_ultra_d D P U) (hV : Rel_ultra_d E Q V)
    (ht : Push_d D E P Q U V t) (hf : Fn0_d D X f) (hg : Fn0_d D X g)
    (hF : Cp0_d E D X t f f') (hG : Cp0_d E D X t g g') :
    (∃ A, M.mem A U ∧ ∀ v, M.mem v A → Rp_atom_d I b X R f g v) ↔
      ∃ B, M.mem B V ∧ ∀ v, M.mem v B → Rp_atom_d I b X R f' g' v := by
  let ρ := (((⟨fun _ => X, fun _ => X⟩ : Env M 1).push R).push f).push g
  let φ : UnarySchema 4 := { body := rp_atom_m (𝒞 := 𝒞) b (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨A, ha⟩ := ZF.separation_exists_d hZF φ ρ D
  have hA v : M.mem v A ↔ M.mem v D ∧ Rp_atom_d I b X R f g v :=
    (ha v).trans (and_congr_right fun _ => rp_atom_sat_l I hZF.1 b _ _ _ _ _ _)
  obtain ⟨B, hBQ, hb, he⟩ := ht.2 A ((hP A).mpr fun v hv => ((hA v).mp hv).1)
  have hB v : M.mem v B ↔ M.mem v E ∧ Rp_atom_d I b X R f' g' v := by
    refine (hb v).trans ⟨?_, ?_⟩
    · rintro ⟨hv, w, hw, hvw⟩
      obtain ⟨_, x, hx, y, hy, hfx, hgy, hxy⟩ := (hA w).mp hw
      exact ⟨hv, x, hx, y, hy, (hF.value_l ht.1 hf hvw).mpr hfx, (hG.value_l ht.1 hg hvw).mpr hgy, hxy⟩
    · rintro ⟨hv, x, hx, y, hy, hfx, hgy, hxy⟩
      obtain ⟨w, hw, hvw⟩ := ht.1.2.1 v hv
      exact ⟨hv, w, (hA w).mpr ⟨hw, x, hx, y, hy, (hF.value_l ht.1 hf hvw).mp hfx,
        (hG.value_l ht.1 hg hvw).mp hgy, hxy⟩, hvw⟩
  have old : M.mem A U ↔ ∃ C, M.mem C U ∧ ∀ v, M.mem v C → Rp_atom_d I b X R f g v :=
    ⟨fun h => ⟨A, h, fun v hv => ((hA v).mp hv).2⟩, fun ⟨C, hC, hh⟩ => hU.upward C A hC
      ((hP A).mpr fun v hv => ((hA v).mp hv).1) (fun v hv => (hA v).mpr ⟨hU.base.bounds C hC v hv, hh v hv⟩)⟩
  have new : M.mem B V ↔ ∃ C, M.mem C V ∧ ∀ v, M.mem v C → Rp_atom_d I b X R f' g' v :=
    ⟨fun h => ⟨B, h, fun v hv => ((hB v).mp hv).2⟩, fun ⟨C, hC, hh⟩ => hV.upward C B hC hBQ
      (fun v hv => (hB v).mpr ⟨hV.base.bounds C hC v hv, hh v hv⟩)⟩
  exact old.symm.trans (he.symm.trans new)

theorem rp_full_projection_l (hZF : M.Models ZF) {D E X R P Q U V t F G c d p q C N S T K : M.Domain}
    (hP : M.IsPowerSetOf P D) (hU : Rel_ultra_d D P U) (hV : Rel_ultra_d E Q V)
    (ht : Push_d D E P Q U V t) (hp : Rp_model_d I D X U R c F p C S) (hq : Rp_model_d I E X V R d G q N T)
    (hK : M.IsSetFunctionFromTo I K F G) (hk : ∀ f g, M.PairMember I f g K → Cp0_d E D X t f g) :
    ∃ j, M.IsSetInjectionFromTo I j C N ∧ Rp_lift_d I K p q j ∧
      ∀ B D B' D', M.PairMember I B B' j → M.PairMember I D D' j →
        (M.PairMember I B D S ↔ M.PairMember I B' D' T) := by
  obtain ⟨j, hj, lift⟩ := rp_lift_exists_l I hZF hU.base hV.base hp.map hq.map hK (fun f g f' g' hf hg =>
    (rp_atom_eq_l I (R := R)).symm.trans ((rp_pull_atom_l I hZF true hP hU hV ht
      (hp.map.functions f (hK.input_mem_of_pairMember hf)) (hp.map.functions g (hK.input_mem_of_pairMember hg))
      (hk f f' hf) (hk g g' hg)).trans (rp_atom_eq_l I)))
  refine ⟨j, hj, lift, fun B D B' D' hBB' hDD' => ?_⟩
  obtain ⟨f, hfp⟩ := (hp.map.range B).mp (hj.1.input_mem_of_pairMember hBB')
  obtain ⟨g, hgp⟩ := (hp.map.range D).mp (hj.1.input_mem_of_pairMember hDD')
  obtain ⟨f', hf', hff'⟩ := hK.2.2 f (hp.map.projection.input_mem_of_pairMember hfp)
  obtain ⟨g', hg', hgg'⟩ := hK.2.2 g (hp.map.projection.input_mem_of_pairMember hgp)
  obtain ⟨B'', _, hfq⟩ := hq.map.projection.2.2 f' hf'
  obtain ⟨D'', _, hgq⟩ := hq.map.projection.2.2 g' hg'
  have eb := hj.1.1.2 B B'' B' (lift f f' B B'' hff' hfp hfq) hBB'
  have ed := hj.1.1.2 D D'' D' (lift g g' D D'' hgg' hgp hgq) hDD'
  subst B'' D''
  exact (hp.relation f g B D hfp hgp).trans ((rp_pull_atom_l I hZF false hP hU hV ht
    (hp.map.functions f (hp.map.projection.input_mem_of_pairMember hfp))
    (hp.map.functions g (hp.map.projection.input_mem_of_pairMember hgp)) (hk f f' hff') (hk g g' hgg')).trans
      (hq.relation f' g' B' D' hfq hgq).symm)

end YesMetaZFC.SetTheory.Internal

/-! ## 原函数重排与对象码代表的同一复合

原函数在所属模型中复合；对象码图的每个取值从已有图读出，因此
新图仍取值于同一共同载体，其当前源代表就是实际过渡得到的代表。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rr_cross_pull_l {N T D E Γ Y k t F g h : M.Domain}
    (nx : ∃ x, M.mem x N) (ext : Extensional (smdl_structure_l I (R := T) nx))
    (d e β p f f' : (smdl_structure_l I (R := T) nx).Domain)
    (fp : Fn0_d e d p) (ff : Fn0_d d β f) (comp : Cp0_d e d β p f f')
    (dc : ∀ s, M.mem s D ↔ M.mem s N ∧ Rd_entry_d s d.val T)
    (ec : ∀ s, M.mem s E ↔ M.mem s N ∧ Rd_entry_d s e.val T)
    (fk : M.IsSetFunctionFromTo I k Γ Y) (fF : Fn0_d D Γ F)
    (gt : ∀ s v : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val v.val t ↔ Rd_entry_d s v p)
    (gF : ∀ s v : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f)
    (value : Cp0_d D Γ Y F k g) (pull : Cp0_d E D Y t g h) :
    ∃ F', Fn0_d E Γ F' ∧
      (∀ s v : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val v.val F' ↔ Rd_entry_d s v f') ∧
      Cp0_d E Γ Y F' k h := by
  let N₀ := smdl_structure_l I (R := T) nx
  obtain ⟨E', B, F', ec', bc, fF', graph⟩ := smdl_graph_l hZF nx ext e β f' comp.1
  have eq := hZF.1.eq_of_same_members E' E (fun x => (ec' x).trans (ec x).symm)
  subst E'
  have fF' := fF'.retarget_l (fun s v hsv => by
    let s' : N₀.Domain := ⟨s, ((ec s).mp (fF'.bound_l hsv).1).1⟩
    let v' : N₀.Domain := ⟨v, ((bc v).mp (fF'.bound_l hsv).2).1⟩
    obtain ⟨u, _, hsu⟩ := fp.2.1 s' ((ec s).mp (fF'.bound_l hsv).1).2
    exact (fF.bound_l ((gF u v').mpr ((comp.value_l fp ff hsu).mp ((graph s' v').mp hsv)))).2)
  refine ⟨F', fF', graph, pull.1, fun s hs => ?_⟩
  obtain ⟨u, hu, y, hy, hsu, huy, hsy⟩ := pull.2 s hs
  let s' : N₀.Domain := ⟨s, ((ec s).mp hs).1⟩
  let u' : N₀.Domain := ⟨u, ((dc u).mp hu).1⟩
  obtain ⟨v, _, huv⟩ := ff.2.1 u' ((dc u).mp hu).2
  have hFv := (gF u' v).mpr huv
  have hsF := (graph s' v).mpr ((comp.value_l fp ff ((gt s' u').mp hsu)).mpr huv)
  exact ⟨v.val, (fF.bound_l hFv).2, y, hy, hsF,
    (value.value_l fF (fn0_of_function_l (ZF.modelsKP hZF) fk) hFv).mp huy, hsy⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 指定约化幂商证书的绝对性

投影的全定义性提供每个类的源内代表。反向识别任意背景等价类时，
直接与该投影值作外延比较，不假设源具有全幂集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {Z : M.Domain}
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
  (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
include hKP hZ
local notation "N" => rt_model_l Z nz
local notation "I" => kp_pair_l hKP
local notation "J" => rt_pair_l hZ nz (And.left hKP) pair

theorem rt_rp_eq_l (Q U f g : (N).Domain) :
    Rp_eq_d Q U f g ↔ Rp_eq_d Q.val U.val f.val g.val := by
  let ρ : Env N 4 := ⟨Fin.cases g (Fin.cases f (Fin.cases U (fun _ => Q))), fun _ => Q⟩
  exact (rp_eq_sat_l (rt_model_ext_l hKP.1 hZ nz) ρ (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
    ((rt_model_delta_l hZ nz (rp_eq_delta_l ..) ρ).trans (rp_eq_sat_l hKP.1 ..))

theorem rt_rp_class_l (Q U G f B : (N).Domain) :
    Rp_class_d Q U G f B ↔ Rp_class_d Q.val U.val G.val f.val B.val := by
  constructor
  · intro h g
    constructor
    · intro hg
      obtain ⟨hG, he⟩ := (h ⟨g, hZ B.val B.property g hg⟩).mp hg
      exact ⟨hG, (rt_rp_eq_l hKP hZ nz ..).mp he⟩
    · rintro ⟨hg, he⟩
      exact (h ⟨g, hZ G.val G.property g hg⟩).mpr ⟨hg, (rt_rp_eq_l hKP hZ nz ..).mpr he⟩
  · intro h g
    exact (h g.val).trans (and_congr Iff.rfl (rt_rp_eq_l hKP hZ nz ..).symm)

theorem rt_rp_map_l (D Q U G p C : (N).Domain) :
    Rp_map_d J D Q U G p C ↔ Rp_map_d I D.val Q.val U.val G.val p.val C.val := by
  have fn := rt_function_from_l hZ nz hKP.1 (KP.exists_pair hKP) pair p G C
  have ran := rt_range_l hZ nz hKP.1 (KP.exists_pair hKP) pair C p
  constructor
  · intro h
    have proj := fn.mp h.projection
    have cls (f B : (N).Domain) := (rt_entry_l hZ nz hKP.1 f B p).symm.trans
      ((h.classes f B).trans (and_congr Iff.rfl (rt_rp_class_l hKP hZ nz Q U G f B)))
    refine ⟨fun f hf => (rt_fn_l hZ nz hKP.1 D Q ⟨f, hZ G.val G.property f hf⟩).mp
      (h.functions _ hf), proj, ran.mp h.range, fun f B => ⟨?_, ?_⟩⟩
    · intro hfB
      have mem := rd_entry_transitive_l hZ p.property hfB
      exact (cls ⟨f, mem.1⟩ ⟨B, mem.2⟩).mp hfB
    · rintro ⟨hf, hb⟩
      obtain ⟨B', hB', hfB'⟩ := proj.2.2 f hf
      have old := ((cls ⟨f, hZ G.val G.property f hf⟩ ⟨B', hZ C.val C.property B' hB'⟩).mp hfB').2
      have eq := hKP.1.eq_of_same_members B B' (fun g => (hb g).trans (old g).symm)
      exact eq.symm ▸ hfB'
  · intro h
    refine ⟨fun f hf => (rt_fn_l hZ nz hKP.1 ..).mpr (h.functions f.val hf),
      fn.mpr h.projection, ran.mpr h.range, fun f B => ?_⟩
    exact (rt_entry_l hZ nz hKP.1 f B p).trans
      ((h.classes f.val B.val).trans (and_congr Iff.rfl (rt_rp_class_l hKP hZ nz Q U G f B).symm))

theorem rt_rp_rel_l (Q U R f g : (N).Domain) :
    Rp_rel_d J Q U R f g ↔ Rp_rel_d I Q.val U.val R.val f.val g.val := by
  constructor
  · rintro ⟨A, hA, h⟩
    refine ⟨A.val, hA, fun i hi => ?_⟩
    obtain ⟨x, hx, y, hy, hix, hiy, hxy⟩ := h ⟨i, hZ A.val A.property i hi⟩ hi
    exact ⟨x.val, hx, y.val, hy, (rt_entry_l hZ nz hKP.1 ..).mp hix,
      (rt_entry_l hZ nz hKP.1 ..).mp hiy, (rt_entry_l hZ nz hKP.1 ..).mp hxy⟩
  · rintro ⟨A, hA, h⟩
    refine ⟨⟨A, hZ U.val U.property A hA⟩, hA, fun i hi => ?_⟩
    obtain ⟨x, hx, y, hy, hix, hiy, hxy⟩ := h i.val hi
    exact ⟨⟨x, hZ Q.val Q.property x hx⟩, hx, ⟨y, hZ Q.val Q.property y hy⟩, hy,
      (rt_entry_l hZ nz hKP.1 ..).mpr hix, (rt_entry_l hZ nz hKP.1 ..).mpr hiy,
      (rt_entry_l hZ nz hKP.1 ..).mpr hxy⟩

theorem rt_rp_model_l (D Q U R c G p C T : (N).Domain) :
    Rp_model_d J D Q U R c G p C T ↔ Rp_model_d I D.val Q.val U.val R.val c.val G.val p.val C.val T.val := by
  constructor
  · intro h
    refine ⟨(rt_rp_map_l hKP hZ nz pair ..).mp h.map, (rt_smdl_l hKP.1 (KP.exists_pair hKP) hZ nz pair ..).mp h.code, ?_⟩
    intro f g B E hf hg
    have fb := rd_entry_transitive_l hZ p.property hf
    have ge := rd_entry_transitive_l hZ p.property hg
    exact (rt_entry_l hZ nz hKP.1 ⟨B, fb.2⟩ ⟨E, ge.2⟩ T).symm.trans
      ((h.relation ⟨f, fb.1⟩ ⟨g, ge.1⟩ ⟨B, fb.2⟩ ⟨E, ge.2⟩ ((rt_entry_l hZ nz hKP.1 ..).mpr hf)
        ((rt_entry_l hZ nz hKP.1 ..).mpr hg)).trans (rt_rp_rel_l hKP hZ nz pair ..))
  · intro h
    refine ⟨(rt_rp_map_l hKP hZ nz pair ..).mpr h.map, (rt_smdl_l hKP.1 (KP.exists_pair hKP) hZ nz pair ..).mpr h.code, ?_⟩
    intro f g B E hf hg
    exact (rt_entry_l hZ nz hKP.1 B E T).trans
      ((h.relation f.val g.val B.val E.val ((rt_entry_l hZ nz hKP.1 ..).mp hf)
        ((rt_entry_l hZ nz hKP.1 ..).mp hg)).trans (rt_rp_rel_l hKP hZ nz pair ..).symm)

end YesMetaZFC.SetTheory.Internal

/-! ## 同一原测度下的原子关系读取

测度集合只沿定义域的完整对象码图取迹。原函数值经共同层实现后，
成员关系由完整前驱方程双向反映，因此几乎处处关系保持同一测度见证。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rr_cross_relation_l {N T D i Γ Y S k V F G f₀ g₀ : M.Domain}
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (d β μ R f g : (smdl_structure_l I (R := T) nx).Domain)
    (member : Rd_fun_d .mem β β β R) (ff : Fn0_d d β f) (fg : Fn0_d d β g)
    (bounded : ∀ A, (smdl_structure_l I (R := T) nx).mem A μ → (smdl_structure_l I (R := T) nx).MemberSubset A d)
    (dc : ∀ s, M.mem s D ↔ M.mem s N ∧ Rd_entry_d s d.val T)
    (fi : M.IsSetFunctionFromTo I i D N) (id : ∀ s x, Rd_entry_d s x i ↔ M.mem s D ∧ s = x)
    (measure : ∀ A, M.mem A V ↔ ∃ B, M.mem B N ∧ Rd_entry_d B μ.val T ∧ Rt_trace_d I D i T B A)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ z, Rd_entry_d z y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s z k)
    (fF : Fn0_d D Γ F) (fG : Fn0_d D Γ G)
    (grF : ∀ s v : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f)
    (grG : ∀ s v : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val v.val G ↔ Rd_entry_d s v g)
    (cf : Cp0_d D Γ Y F k f₀) (cg : Cp0_d D Γ Y G k g₀) :
    Rp_rel_d (kp_pair_l hN) β μ R f g ↔ Rp_rel_d I Y V S f₀ g₀ := by
  let N₀ := smdl_structure_l I (R := T) nx
  have key := fn0_of_function_l (ZF.modelsKP hZF) fk.1
  have atoms (x y : N₀.Domain) x' y' (hx : N₀.mem x β) (hy : N₀.mem y β)
      (hxx : Rd_entry_d x.val x' k) (hyy : Rd_entry_d y.val y' k) :
      Rd_entry_d x y R ↔ Rd_entry_d x' y' S :=
    (rt_mem_graph_l hN member x y).trans ((and_iff_right hx).trans ((and_iff_right hy).trans
      ⟨fun h => (pred y.val y' hyy x').mpr ⟨x.val, h, hxx⟩, fun h => by
        obtain ⟨v, hv, hvx⟩ := (pred y.val y' hyy x').mp h
        change Rd_entry_d x.val y.val T
        exact fk.2 v x.val x' hvx hxx ▸ hv⟩))
  constructor
  · rintro ⟨A, hA, point⟩
    obtain ⟨B, trace⟩ := rt_trace_exists_l I hZF D i T A.val
    refine ⟨B, (measure B).mpr ⟨A.val, A.property, hA, trace⟩, fun s hs => ?_⟩
    have hsD := ((trace s).mp hs).1
    let s' : N₀.Domain := ⟨s, ((dc s).mp hsD).1⟩
    have hsA : N₀.mem s' A := (trace.value_l I fi ((id s s).mpr ⟨hsD, rfl⟩)).mp hs
    obtain ⟨x, hx, y, hy, hsx, hsy, hxy⟩ := point s' hsA
    have hFx := (grF s' x).mpr hsx
    have hGy := (grG s' y).mpr hsy
    obtain ⟨x', hx', hxx⟩ := fk.1.2.2 x.val (fF.bound_l hFx).2
    obtain ⟨y', hy', hyy⟩ := fk.1.2.2 y.val (fG.bound_l hGy).2
    exact ⟨x', hx', y', hy', (cf.value_l fF key hFx).mpr hxx, (cg.value_l fG key hGy).mpr hyy,
      (atoms x y x' y' hx hy hxx hyy).mp hxy⟩
  · rintro ⟨B, hB, point⟩
    obtain ⟨A, hA, hAμ, trace⟩ := (measure B).mp hB
    let A' : N₀.Domain := ⟨A, hA⟩
    refine ⟨A', hAμ, fun s hs => ?_⟩
    have hsd := bounded A' hAμ s hs
    have hsD := (dc s.val).mpr ⟨s.property, hsd⟩
    have hsB := (trace.value_l I fi ((id s.val s.val).mpr ⟨hsD, rfl⟩)).mpr hs
    obtain ⟨x, hx, hsx⟩ := ff.2.1 s hsd
    obtain ⟨y, hy, hsy⟩ := fg.2.1 s hsd
    obtain ⟨x', _, y', _, hsx', hsy', hxy'⟩ := point s.val hsB
    have hxx := (cf.value_l fF key ((grF s x).mpr hsx)).mp hsx'
    have hyy := (cg.value_l fG key ((grG s y).mpr hsy)).mp hsy'
    exact ⟨x, hx, y, hy, hsx, hsy, (atoms x y x' y' hx hy hxx hyy).mpr hxy'⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 几乎处处有界的代表可在源内改成处处有界

在不满足界的坐标上取给定基点。新图由源内统一化实际构造；等价只使用
原来的测度一集合，不要求源拥有背景中的全部函数或全部子集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_bound_l {ω c X R D B U f z : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (hD : M.mem D X) (hB : M.mem B X)
    (hfX : M.mem f X) (hf : Fn0_d D X f) (hz : M.mem z B) (hU : ∀ A, M.mem A U → M.MemberSubset A D)
    (bounded : ∃ A, M.mem A U ∧ ∀ v, M.mem v A → ∃ x, M.mem x B ∧ Rd_entry_d v x f) :
    ∃ g, M.mem g X ∧ Fn0_d D B g ∧ Rp_eq_d X U f g := by
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases B (fun _ => z)), fun _ => z⟩
  let φ : BinarySchema 3 := {
    body := .disj (.conj (.mem .newest (.bound 3)) (rd_entry0_m (.bound 1) .newest (.bound 2)))
      (.conj (.neg (Formula.existsMem (.bound 3) (rd_entry0_m (.bound 2) .newest (.bound 3))))
        (Formula.extensionalEq .newest (.bound 4))) }
  have sat v x : φ.denote ρ v x ↔ (M.mem x B ∧ Rd_entry_d v x f) ∨
      (¬ (∃ y, M.mem y B ∧ Rd_entry_d v y f) ∧ x = z) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_existsMem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨g, hgX, hg, select⟩ := sc_uniform_source_l hZF hω hX hm theory φ
    (.disj (.conj (.mem _ _) (rd_entry0_delta_l ..))
      (.conj (.neg (.existsMem _ (rd_entry0_delta_l ..))) (.atom _ _ _))) ρ
    (Fin.cases hfX (Fin.cases hB (fun _ => hX B hB z hz))) hD hB (fun v _ => by
      classical
      by_cases h : ∃ y, M.mem y B ∧ Rd_entry_d v y f
      · obtain ⟨y, hy, hvy⟩ := h
        exact ⟨y, hy, (sat v y).mpr (Or.inl ⟨hy, hvy⟩)⟩
      · exact ⟨z, hz, (sat v z).mpr (Or.inr ⟨h, rfl⟩)⟩)
  obtain ⟨A, hAU, bound⟩ := bounded
  refine ⟨g, hgX, hg, A, hAU, fun v hv => ?_⟩
  obtain ⟨x, hxB, hvx⟩ := bound v hv
  obtain ⟨y, _, hvy⟩ := hg.2.1 v (hU A hAU v hv)
  rcases (sat v y).mp (select v y hvy) with ⟨_, hvy'⟩ | ⟨hn, _⟩
  · exact ⟨x, hX B hB x hxB, hvx, (fn0_function_l (ZF.modelsKP hZF) hf).1.2 v y x hvy' hvx ▸ hvy⟩
  · exact (hn ⟨x, hxB, hvx⟩).elim

/-- 对集合值代表逐点取交；几乎处处已在界内时，商中的值不变。 -/
theorem rs_cap_l {ω c X R D B U f : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (hD : M.mem D X) (hB : M.mem B X)
    (hfX : M.mem f X) (hf : Fn0_d D X f) (hU : ∀ A, M.mem A U → M.MemberSubset A D)
    (bounded : ∃ A, M.mem A U ∧ ∀ s x, M.mem s A → Rd_entry_d s x f → M.MemberSubset x B) :
    ∃ g, M.mem g X ∧ Fn0_d D X g ∧
      (∀ s x, Rd_entry_d s x g → M.MemberSubset x B) ∧ Rp_eq_d X U f g := by
  obtain ⟨_, C, hCX, hfC⟩ := sc_function_domain_l (theory.algebra_l _ (ZF.modelsKP hZF) hX hm) hfX hf
  let ρ : Env M 2 := ⟨Fin.cases f (fun _ => C), fun _ => f⟩
  let φ : BinarySchema 2 := {
    body := Formula.existsMem (.bound 3) (.conj (rd_entry0_m (.bound 2) .newest (.bound 3)) (.mem (.bound 1) .newest)) }
  have sat s z : φ.denote ρ s z ↔ ∃ x, M.mem x C ∧ Rd_entry_d s x f ∧ M.mem z x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  obtain ⟨g, H, hgX, hHX, hg, row⟩ := sc_separation_function_l hZF hω hX hm theory φ
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (.mem _ _))) ρ (Fin.cases hfX (fun _ => hCX)) hD hB
  obtain ⟨A, hAU, bound⟩ := bounded
  refine ⟨g, hgX, hg.mono_target_l (hX H hHX),
    (fun s y hsy z hz => ((row s y hsy z).mp hz).1), A, hAU, fun s hs => ?_⟩
  obtain ⟨y, _, hsy⟩ := hg.2.1 s (hU A hAU s hs)
  obtain ⟨x, hx, hsx⟩ := hfC.2.1 s (hU A hAU s hs)
  have eq : y = x := hZF.1.eq_of_same_members y x fun z => by
    rw [row s y hsy z, sat s z]
    refine ⟨fun ⟨_, t, _, hst, hzt⟩ => (fn0_function_l (ZF.modelsKP hZF) hf).1.2 s t x hst hsx ▸ hzt,
      fun hz => ⟨bound s x hs hsx z hz, x, hx, hsx, hz⟩⟩
  exact ⟨x, hX C hCX x hx, hsx, eq ▸ hsy⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 源内有界约化幂

候选函数集、值域和滤子属于源时，等价类投影与商关系也属于源。
只有收集全部源内有界函数需要相对幂集；商构造本身只用有界分离与纤维。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_map_source_l {ω c X S D Q U G : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X S) (theory : Sc_theory_d I ω X S)
    (hQ : M.mem Q X) (hU : M.mem U X) (hG : M.mem G X) (functions : ∀ f, M.mem f G → Fn0_d D Q f) :
    ∃ p C, M.mem p X ∧ M.mem C X ∧ Rp_map_d I D Q U G p C := by
  let ρ : Env M 2 := ⟨Fin.cases Q (fun _ => U), fun _ => Q⟩
  let φ : BinarySchema 2 := { body := rp_eq_m (.bound 2) (.bound 3) (.bound 1) .newest }
  obtain ⟨p, B, hp, _, fn, classes⟩ := sc_separation_function_l hZF hω hX hm theory φ
    (rp_eq_delta_l ..) ρ (Fin.cases hQ (fun _ => hU)) hG hG
  have cl f E (he : Rd_entry_d f E p) : Rp_class_d Q U G f E :=
    fun g => (classes f E he g).trans (and_congr_right fun _ => rp_eq_sat_l hZF.1 ..)
  obtain ⟨C, hC, range⟩ := sc_range_source_l hZF hω hX hm theory hp
  refine ⟨p, C, hp, hC, ⟨functions, fn0_function_l (ZF.modelsKP hZF)
    (fn.retarget_l (fun f E he => (range E).mpr ⟨f, he⟩)), range, fun f E => ⟨?_, ?_⟩⟩⟩
  · intro he
    exact ⟨(fn.bound_l he).1, cl f E he⟩
  · rintro ⟨hf, he⟩
    obtain ⟨B, _, hb⟩ := fn.2.1 f hf
    exact hZF.1.eq_of_same_members B E (fun g => (cl f B hb g).trans (he g).symm) ▸ hb

theorem rs_model_source_l {ω c X S D Q U G R : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X S) (theory : Sc_theory_d I ω X S)
    (hQ : M.mem Q X) (hU : M.mem U X) (hG : M.mem G X) (hR : M.mem R X)
    (base : FilterZF.Base_d (ℳ := M) D U) (functions : ∀ f, M.mem f G → Fn0_d D Q f)
    (inhabited : ∃ f, M.mem f G) : ∃ d p C T, M.mem d X ∧ M.mem p X ∧ M.mem C X ∧ M.mem T X ∧
      Rp_model_d I D Q U R d G p C T := by
  obtain ⟨p, C, hp, hC, map⟩ := rs_map_source_l hZF hω hX hm theory hQ hU hG functions
  let ρ : Env M 5 := ⟨Fin.cases p (Fin.cases G (Fin.cases Q (Fin.cases U (fun _ => R)))), fun _ => Q⟩
  -- 所有代表元、滤子成员及函数值都有现成的源内界。
  let φ : BinarySchema 5 := { body := Formula.existsMem (.bound 3) (Formula.existsMem (.bound 4)
    (.conj (rd_entry0_m (.bound 1) (.bound 3) (.bound 4)) (.conj
      (rd_entry0_m .newest (.bound 2) (.bound 4))
      (Formula.existsMem (.bound 7) (Formula.forallMem .newest
        (Formula.existsMem (.bound 8) (Formula.existsMem (.bound 9)
          (.conj (rd_entry0_m (.bound 2) (.bound 1) (.bound 5))
            (.conj (rd_entry0_m (.bound 2) .newest (.bound 4))
              (rd_entry0_m (.bound 1) .newest (.bound 12))))))))))) }
  have sat B E : φ.denote ρ B E ↔ ∃ f, M.mem f G ∧ ∃ g, M.mem g G ∧
      Rd_entry_d f B p ∧ Rd_entry_d g E p ∧ Rp_rel_d I Q U R f g := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1, Rp_rel_d]; rfl
  have delta : φ.body.IsDelta0 := .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..)
    (.conj (rd_entry0_delta_l ..) (.existsMem _ (.forallMem _ (.existsMem _ (.existsMem _
      (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))))
  obtain ⟨T, hT, relation, spec⟩ := sc_relation_source_l hZF hω hX hm theory φ delta ρ
    (Fin.cases hp (Fin.cases hG (Fin.cases hQ (Fin.cases hU (fun _ => hR))))) hC hC
  obtain ⟨d, hd, code⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX hm).kpair_l hC hT
  obtain ⟨f, hf⟩ := inhabited
  obtain ⟨B, hb, _⟩ := map.projection.2.2 f hf
  refine ⟨d, p, C, T, hd, hp, hC, hT, ⟨map, ⟨code, ⟨B, hb⟩, relation,
    fun B E he => ⟨((spec B E).mp he).1, ((spec B E).mp he).2.1⟩⟩, fun f g B E hf hg => ?_⟩⟩
  change Rd_entry_d B E T ↔ _
  rw [spec B E, sat B E]
  constructor
  · rintro ⟨_, _, f', hfG, g', hgG, hf', hg', hfg⟩
    exact rp_rel_transport_l I base (functions f' hfG) (functions g' hgG)
      ((rp_kernel_l I hZF.1 base map hf' hf).mp rfl) ((rp_kernel_l I hZF.1 base map hg' hg).mp rfl) hfg
  · intro hfg
    exact ⟨map.projection.output_mem_of_pairMember hf, map.projection.output_mem_of_pairMember hg,
      f, map.projection.input_mem_of_pairMember hf, g, map.projection.input_mem_of_pairMember hg, hf, hg, hfg⟩

/-- 源中非空的值域给出常值代表，进而实际生成整个有界商。 -/
theorem rs_bounded_model_l {ω c X S D Q U R : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X S) (theory : Sc_theory_d I ω X S) (power : Sc_power_d X)
    (hD : M.mem D X) (hQ : M.mem Q X) (hU : M.mem U X) (hR : M.mem R X)
    (base : FilterZF.Base_d (ℳ := M) D U) (inhabited : ∃ x, M.mem x Q) : ∃ G d p C T,
      M.mem G X ∧ M.mem d X ∧ M.mem p X ∧ M.mem C X ∧ M.mem T X ∧
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D Q f) ∧ Rp_model_d I D Q U R d G p C T := by
  obtain ⟨G, hG, functions⟩ := sc_function_space_l hZF hω hX hm theory power hD hQ
  obtain ⟨x, hx⟩ := inhabited
  obtain ⟨f, A, hf, _, fn, value⟩ := sc_constant_l hZF hω hX hm theory hD (hX Q hQ x hx)
  have hfG : M.mem f G := (functions f).mpr ⟨hf, fn.retarget_l (fun a b hab => ((value a b).mp hab).2 ▸ hx)⟩
  obtain ⟨d, p, C, T, hd, hp, hC, hT, model⟩ := rs_model_source_l hZF hω hX hm theory hQ hU hG hR base
    (fun f hf => ((functions f).mp hf).2) ⟨f, hfG⟩
  exact ⟨G, d, p, C, T, hG, hd, hp, hC, hT, functions, model⟩

end YesMetaZFC.SetTheory.Internal
