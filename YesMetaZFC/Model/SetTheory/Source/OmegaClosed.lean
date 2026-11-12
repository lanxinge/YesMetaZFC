import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.Hereditary
import YesMetaZFC.SetTheory.Collapse.RelationSequence
import YesMetaZFC.SetTheory.HereditaryFunction
import YesMetaZFC.SetTheory.CumulativeClosure
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.SetTheory.InnerModel.Order.Coordinates
import YesMetaZFC.Model.SetTheory.Source.Theory
import YesMetaZFC.Model.SetTheory.Source.Relation
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.SetTheory.CumulativeRelativeClosure
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize
import YesMetaZFC.SetTheory.CumulativeFunction
import YesMetaZFC.SetTheory.Notation

/-! # 源内传递包络

每个源内集合的成员同时落在一个源内传递集合中。秩层直接取较早层，
初等传输覆盖全部新参数；相对秩段直接读取原历史，无需增加正则性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_cover_d (X : M.Domain) : Prop := ∀ A, M.mem A X →
  ∃ T, M.mem T X ∧ M.TransitiveSet T ∧ M.MemberSubset A T

def sc_cover_m : Formula 1 0 := .forallE (.existsE
  (.conj (Formula.isTransitive .newest) (Formula.subset (.bound 1) .newest)))
derive_free_closed sc_cover_m

theorem sc_cover_sat_l {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x // M.mem x X}) (ρ : Env (rt_model_l X hn) 0) :
    Formula.satisfies ρ sc_cover_m ↔ Sc_cover_d X := by
  have matrix (η : Env (rt_model_l X hn) 2) : Formula.satisfies η
      (.conj (Formula.isTransitive .newest) (Formula.subset (.bound 1) .newest)) ↔
      M.TransitiveSet (η.bound 0).val ∧ M.MemberSubset (η.bound 1).val (η.bound 0).val :=
    (rt_model_delta_l hX hn (.conj (.forallMem _ (.forallMem _ (.mem ..))) (.atom ..)) η).trans
      ((Formula.satisfies_conj_iff ..).trans (and_congr (Formula.satisfies_isTransitive_iff ..) (Formula.satisfies_subset_iff ..)))
  simp only [sc_cover_m, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff, matrix]
  exact ⟨fun h A hA => (h ⟨A, hA⟩).elim fun T ht => ⟨T.val, T.property, ht⟩,
    fun h A => (h A.val A.property).elim fun T ht => ⟨⟨T, ht.1⟩, ht.2⟩⟩

theorem sc_v_cover_l (hZF : M.Models ZF) {δ X : M.Domain}
    (hx : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) : Sc_cover_d X := by
  intro A hA
  obtain ⟨β, T, hβ, ht, sub⟩ := (ZF.v_unfold_l _ hZF hx A).mp hA
  exact ⟨T, ZF.v_mem_l _ hZF ht hx hβ, v_transitive_l _ ht, sub⟩

theorem sc_h_cover_l (hZF : M.Models ZF) {χ X : M.Domain} (hχ : M.IsLimitOrdinal χ)
    (hx : H_d (kp_pair_l (ZF.modelsKP hZF)) χ X) : Sc_cover_d X := by
  intro A hA
  obtain ⟨T, μ, ht, hμ, size⟩ := (hx A).mp hA
  exact ⟨T, (hx T).mpr (ZF.hmem_of_subset_l _ hZF hχ ht.1 (fun _ h => h) hμ size), ht.1, ht.1 A ht.2.1⟩

theorem sc_cover_iff_l (hZF : M.Models ZF) {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) : Sc_cover_d X ↔ Sc_cover_d Y := by
  obtain ⟨x, hx⟩ := hm.1.2.1
  obtain ⟨y, hy⟩ := hn.1.2.1
  let nx : Nonempty {a // M.mem a X} := ⟨⟨x, hx⟩⟩
  let ny : Nonempty {a // M.mem a Y} := ⟨⟨y, hy⟩⟩
  let ρ : Env (rt_model_l X nx) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
  let η : Env (rt_model_l Y ny) 0 := ⟨Fin.elim0, fun _ => ⟨y, hy⟩⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ he, hn.empty_pred_l _ he, hj⟩ nx ny
    sc_cover_m (by simp -implicitDefEqProofs [sc_cover_m, Definitional.Formula.FreeClosed]) ρ η (fun i => Fin.elim0 i)
  exact (sc_cover_sat_l hX nx ρ).symm.trans (tr.trans (sc_cover_sat_l hY ny η))

theorem sc_rank_cover_l {Z α V : M.Domain}
    (hZ : M.TransitiveSet Z) (hV : M.mem V Z) (rank : Vr_d Z α V) : Sc_cover_d V := by
  obtain ⟨B, F, hB, _, cert⟩ := rank
  intro A hA
  obtain ⟨β, hβ, T, hT, hβT, sub⟩ := ((cert A (hZ V hV A hA)).2.2.2).mp hA
  exact ⟨T, ((cert T (hZ B hB T hT)).2.2.2).mpr ⟨β, hβ, T, hT, hβT, fun _ h => h⟩,
    (vc_transitive_l hZ hV hB cert).2 β hβ T hβT, sub⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 外部下降链的源内反射

此处直接陈述背景中存在下降链时源内也存在一条。Hχ 与 Vδ 的实例由实际
函数图闭包给出；该外部性质不随一般初等映射自动传递。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_branch_d (ω X : M.Domain) : Prop := ∀ A R, M.mem A X → M.mem R X →
  (∃ f, Fn0_d ω A f ∧ Wf_desc_d R f) → ∃ f, M.mem f X ∧ Fn0_d ω A f ∧ Wf_desc_d R f

theorem sc_h_branch_l (hZFC : M.Models ZFC) {ω χ H : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H)
    (hωH : M.mem ω H) : Sc_branch_d ω H := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro A R hA _ ⟨f, hf, hd⟩
  exact ⟨f, ZFC.h_function_l hZFC hω hχ hωχ hH hωH
    (fn0_function_l (ZF.modelsKP hZF) (hf.mono_target_l (ZF.h_transitive_l I hZF hH A hA))), hf, hd⟩

theorem sc_v_branch_l (hZF : M.Models ZF) {ω δ V : M.Domain} (hδ : M.IsLimitOrdinal δ)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ V) (hωV : M.mem ω V) : Sc_branch_d ω V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro A R hA _ ⟨f, hf, hd⟩
  obtain ⟨Y, hY, hωY, hAY⟩ := v_joint_bound_l I hV hωV hA
  exact ⟨f, v_relation_mem_l I hV hδ hY (fun p hp =>
    (hf.1 p hp).elim fun i hi => hi.2.elim fun a ha => ⟨i, hωY i hi.1, a, hAY a ha.1, ha.2⟩), hf, hd⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 枝反射的可定义良基关系

把模型内没有下降枝的每个关系加上固定标签。标签包含载体、关系和当前点，
原二元公式由此同时处理所有源内关系，供超幂的共同纤维论证使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sb_chain_d (ω A R f : M.Domain) : Prop := Fn0_d ω A f ∧ Wf_desc_d R f

def sb_chain_m {n} (ω A R f : Term n) : Formula 1 n := .conj (fn0_m ω A f)
  (Formula.forallMem ω (Formula.forallMem ω.weaken (Formula.forallMem A.weaken.weaken
    (Formula.forallMem A.weaken.weaken.weaken (.imp (KP.succ0_m (.bound 2) (.bound 3))
      (.imp (rd_entry0_m (.bound 3) (.bound 1) f.weaken.weaken.weaken.weaken)
        (.imp (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken.weaken)
          (rd_entry0_m .newest (.bound 1) R.weaken.weaken.weaken.weaken))))))))
derive_free_closed sb_chain_m

theorem sb_chain_delta_l {n} (ω A R f : Term n) : (sb_chain_m ω A R f).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (KP.succ0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))

theorem sb_chain_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω A R f : Term n) :
    Formula.satisfies ρ (sb_chain_m ω A R f) ↔ Sb_chain_d (ω.eval ρ) (A.eval ρ) (R.eval ρ) (f.eval ρ) := by
  simp only [sb_chain_m, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, KP.succ0_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨hf, h⟩ => ⟨hf, fun i j x y hs hx hy => h i (hf.bound_l hx).1 j (hf.bound_l hy).1
    x (hf.bound_l hx).2 y (hf.bound_l hy).2 hs hx hy⟩,
    fun ⟨hf, hd⟩ => ⟨hf, fun i _ j _ x _ y _ => hd i j x y⟩⟩

def Sb_edge_d (A R u v : M.Domain) : Prop := ∃ x, M.mem x A ∧ ∃ y, M.mem y A ∧
  Rd_triple_d u A R x ∧ Rd_triple_d v A R y ∧ Rd_entry_d x y R

def sb_edge_m {n} (ω A R u v : Term n) : Formula 1 n := .conj (omega0_m ω)
  (Formula.existsMem A (Formula.existsMem A.weaken
    (.conj (rd_triple0_m u.weaken.weaken A.weaken.weaken R.weaken.weaken (.bound 1))
      (.conj (rd_triple0_m v.weaken.weaken A.weaken.weaken R.weaken.weaken .newest)
        (rd_entry0_m (.bound 1) .newest R.weaken.weaken)))))
derive_free_closed sb_edge_m

theorem sb_edge_delta_l {n} (ω A R u v : Term n) : (sb_edge_m ω A R u v).IsDelta0 :=
  .conj (omega0_delta_l _) (.existsMem _ (.existsMem _ (.conj (rd_triple0_delta_l ..)
    (.conj (rd_triple0_delta_l ..) (rd_entry0_delta_l ..)))))

theorem sb_edge_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω A R u v : Term n) :
    Formula.satisfies ρ (sb_edge_m ω A R u v) ↔ Omega0_d (ω.eval ρ) ∧
      Sb_edge_d (A.eval ρ) (R.eval ρ) (u.eval ρ) (v.eval ρ) := by
  simp only [sb_edge_m, Sb_edge_d, Formula.satisfies_conj_iff, omega0_sat_l hE,
    Formula.satisfies_existsMem_iff, rd_triple0_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Sb_bad_d (ω X u v : M.Domain) : Prop := ∃ A R, M.mem A X ∧ M.mem R X ∧
  Sb_edge_d A R u v ∧ ¬ ∃ f, M.mem f X ∧ Sb_chain_d ω A R f

def sb_bad_m : Formula 1 2 := .existsE (.existsE (.existsE
  (.conj (sb_edge_m (.bound 2) (.bound 1) .newest (.bound 4) (.bound 3))
    (.neg (.existsE (sb_chain_m (.bound 3) (.bound 2) (.bound 1) .newest))))))

theorem sb_bad_closed_l : sb_bad_m.FreeClosed := by
  simp -implicitDefEqProofs [sb_bad_m, Definitional.Formula.FreeClosed]

theorem sb_bad_sat_l (hZF : M.Models ZF) {ω c X R : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hωX : M.mem ω X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (ρ : Env (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) hm.1.2.1) 2) :
    Formula.satisfies ρ sb_bad_m ↔ Sb_bad_d ω X (ρ.bound 1).val (ρ.bound 0).val := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let N := smdl_structure_l I (R := R) hm.1.2.1
  have edge (η : Env N 5) := (smem_delta_image_l I hm hX
    (sb_edge_delta_l (.bound 2) (.bound 1) .newest (.bound 4) (.bound 3)) η).trans (sb_edge_sat_l hZF.1 ..)
  have chain (η : Env N 6) := (smem_delta_image_l I hm hX
    (sb_chain_delta_l (.bound 3) (.bound 2) (.bound 1) .newest) η).trans (sb_chain_sat_l hZF.1 ..)
  simp only [sb_bad_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, edge, chain]
  constructor
  · rintro ⟨Ω, A, S, ⟨ho, he⟩, no⟩
    have eq := (omega0_iff_l (ZF.models_kpi_l hZF) hω).mp ho
    exact ⟨A.val, S.val, A.property, S.property, he, fun ⟨f, hf, h⟩ => no ⟨⟨f, hf⟩, eq.symm ▸ h⟩⟩
  · rintro ⟨A, S, hA, hS, he, no⟩
    exact ⟨⟨ω, hωX⟩, ⟨A, hA⟩, ⟨S, hS⟩, ⟨(omega0_iff_l (ZF.models_kpi_l hZF) hω).mpr rfl, he⟩,
      fun ⟨f, hf⟩ => no ⟨f.val, f.property, hf⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 枝反射与统一标签关系的良基性

每条标签关系的下降都保持原载体和原关系。枝反射排除这样的下降；反向则
给任何外部下降枝逐点加标签，用统一关系的良基性迫使源内已经存在枝。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem sb_bad_wf_l {ω X Q : M.Domain} (hDC : Dc_d I ω) (branches : Sc_branch_d ω X)
    (rel : ∀ u v, M.mem u X → M.mem v X → (Rd_entry_d u v Q ↔ Sb_bad_d ω X u v)) : Wf_rel_d X Q := by
  intro B sub ⟨u, hu⟩
  apply Classical.byContradiction
  intro no
  have prev v (hv : M.mem v B) : ∃ w, M.mem w B ∧ Rd_entry_d w v Q := by
    apply Classical.byContradiction
    intro nh
    exact no ⟨v, hv, fun w hw hr => nh ⟨w, hw, hr⟩⟩
  obtain ⟨v, hv, hvu⟩ := prev u hu
  obtain ⟨A, R, hA, hR, ⟨x, _, y, hy, _, hty, _⟩, absent⟩ := (rel v u (sub v hv) (sub u hu)).mp hvu
  have wf : Wf_rel_d A R := wf_of_no_desc_l hZF hDC
    (fun f hf hd => absent (branches A R hA hR ⟨f, hf, hd⟩))
  let φ : UnarySchema 3 := {
    body := Formula.existsMem (.bound 1) (rd_triple0_m .newest (.bound 3) (.bound 4) (.bound 1)) }
  let ρ : Env M 3 := ⟨Fin.cases B (Fin.cases A (fun _ => R)), fun _ => B⟩
  obtain ⟨C, spec⟩ := ZF.separation_exists_d hZF φ ρ A
  have cs z : M.mem z C ↔ M.mem z A ∧ ∃ w, M.mem w B ∧ Rd_triple_d w A R z := by
    simpa only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, rd_triple0_sat_l hZF.1] using! spec z
  obtain ⟨z, hz, least⟩ := wf C (fun z hz => ((cs z).mp hz).1) ⟨y, (cs y).mpr ⟨hy, u, hu, hty⟩⟩
  obtain ⟨_, w, hw, htw⟩ := (cs z).mp hz
  obtain ⟨v, hv, hvw⟩ := prev w hw
  obtain ⟨A', R', _, _, ⟨x', hx', y', _, htx, hty', hr⟩, _⟩ := (rel v w (sub v hv) (sub w hw)).mp hvw
  obtain ⟨ea, er, ey⟩ := pc_triple_inj_l hty' htw
  subst A' R' y'
  exact least x' ((cs x').mpr ⟨hx', v, hv, htx⟩) hr

theorem sb_bad_branch_l {ω X Q : M.Domain} (hω : M.IsOmega ω) (hX : M.TransitiveSet X)
    (algebra : Sc_algebra_d X) (wf : Wf_rel_d X Q)
    (rel : ∀ u v, M.mem u X → M.mem v X → (Rd_entry_d u v Q ↔ Sb_bad_d ω X u v)) : Sc_branch_d ω X := by
  intro A R hA hR ⟨f, hf, hd⟩
  apply Classical.byContradiction
  intro absent
  have tag x (hx : M.mem x A) : ∃ u, M.mem u X ∧ Rd_triple_d u A R x := by
    obtain ⟨v, hv, hc⟩ := algebra.kpair_l hR (hX A hA x hx)
    obtain ⟨u, hu, he⟩ := algebra.kpair_l hA hv
    exact ⟨u, hu, v, hc, he⟩
  let φ : BinarySchema 3 := { body := .existsE (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
    (rd_triple0_m (.bound 1) (.bound 4) (.bound 5) .newest)) }
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases A (fun _ => R)), fun _ => f⟩
  have val i u : φ.denote ρ i u ↔ ∃ x, Rd_entry_d i x f ∧ Rd_triple_d u A R x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, rd_triple0_sat_l hZF.1]; rfl
  obtain ⟨g, hg, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X)
    (fun i hi => by
      obtain ⟨x, hx, hix⟩ := hf.2.1 i hi
      obtain ⟨u, _, hu⟩ := tag x hx
      exact ⟨u, (val i u).mpr ⟨x, hix, hu⟩⟩)
    (fun i _ u v hu hv => by
      obtain ⟨x, hix, hx⟩ := (val i u).mp hu
      obtain ⟨y, hiy, hy⟩ := (val i v).mp hv
      have eq := (fn0_function_l (ZF.modelsKP hZF) hf).1.2 i y x hiy hix
      exact pn_triple_unique_l hZF.1 hx (eq ▸ hy))
    (fun i u _ hu => by
      obtain ⟨x, hix, hx⟩ := (val i u).mp hu
      obtain ⟨v, hv, ht⟩ := tag x (hf.bound_l hix).2
      exact pn_triple_unique_l hZF.1 ht hx ▸ hv)
  apply wf_no_desc_l hZF hω wf (fn0_of_function_l (ZF.modelsKP hZF) hg)
  intro i m u v hmi hiu hmv
  obtain ⟨x, hix, htx⟩ := (val i u).mp ((gs i u).mp hiu).2
  obtain ⟨y, hmy, hty⟩ := (val m v).mp ((gs m v).mp hmv).2
  exact (rel v u (hg.output_mem_of_pairMember hmv) (hg.output_mem_of_pairMember hiu)).mpr
    ⟨A, R, hA, hR, ⟨y, (hf.bound_l hmy).2, x, (hf.bound_l hix).2, hty, htx, hd i m x y hmi hix hmy⟩, absent⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 无枝标签关系的源内前驱封闭界

将源内传递包络 T 与 T 中三个坐标的全部标签合并。这个实际集合在标签
关系的前驱下封闭，其有界规格沿原初等嵌入保持；无枝条件仍按源真值分离。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sb_hull_d (T B : M.Domain) : Prop := M.TransitiveSet T ∧ M.MemberSubset T B ∧
  (∀ u, M.mem u B → M.mem u T ∨ ∃ A, M.mem A T ∧ ∃ R, M.mem R T ∧ ∃ x, M.mem x T ∧ Rd_triple_d u A R x) ∧
  ∀ A, M.mem A T → ∀ R, M.mem R T → ∀ x, M.mem x T → ∃ u, M.mem u B ∧ Rd_triple_d u A R x

def sb_hull_m {d} (T B : Term d) : Formula 1 d := .conj (Formula.isTransitive T) (.conj (Formula.subset T B)
  (.conj (Formula.forallMem B (.disj (.mem .newest T.weaken)
    (Formula.existsMem T.weaken (Formula.existsMem T.weaken.weaken (Formula.existsMem T.weaken.weaken.weaken
      (rd_triple0_m (.bound 3) (.bound 2) (.bound 1) .newest))))))
    (Formula.forallMem T (Formula.forallMem T.weaken (Formula.forallMem T.weaken.weaken
      (Formula.existsMem B.weaken.weaken.weaken (rd_triple0_m .newest (.bound 3) (.bound 2) (.bound 1))))))))
derive_free_closed sb_hull_m

theorem sb_hull_delta_l {d} (T B : Term d) : (sb_hull_m T B).IsDelta0 := by
  refine .conj (.forallMem _ (.forallMem _ (.mem ..))) (.conj (.atom ..) (.conj ?_ ?_))
  · exact .forallMem _ (.disj (.mem ..) (.existsMem _ (.existsMem _ (.existsMem _ (rd_triple0_delta_l ..)))))
  · exact .forallMem _ (.forallMem _ (.forallMem _ (.existsMem _ (rd_triple0_delta_l ..))))

theorem sb_hull_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T B : Term d) :
    Formula.satisfies ρ (sb_hull_m T B) ↔ Sb_hull_d (T.eval ρ) (B.eval ρ) := by
  simp only [sb_hull_m, Sb_hull_d, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, rd_triple0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Sb_hull_d.closed_l (hE : Extensional M) {T B A R u v : M.Domain}
    (h : Sb_hull_d T B) (hv : M.mem v B) (edge : Sb_edge_d A R u v) : M.mem u B := by
  obtain ⟨x, hx, y, _, ux, vy, _⟩ := edge
  have coords {z a b : M.Domain} (hz : M.mem z T) (pair : KPair_d M z a b) : M.mem a T ∧ M.mem b T := by
    have bound k (hk : k = a ∨ k = b) : M.mem k T := by
      obtain ⟨s, hs, hks⟩ := (kpair_union_l M pair k).mpr hk
      exact h.1 s (h.1 z hz s hs) k hks
    exact ⟨bound a (Or.inl rfl), bound b (Or.inr rfl)⟩
  have labels : M.mem A T ∧ M.mem R T := by
    rcases h.2.2.1 v hv with hv | ⟨A', ha, R', hr, x', _, vt⟩
    · obtain ⟨q, qr, vq⟩ := vy
      have aq := coords hv vq
      exact ⟨aq.1, (coords aq.2 qr).1⟩
    · obtain ⟨rfl, rfl, _⟩ := pc_triple_inj_l vt vy
      exact ⟨ha, hr⟩
  obtain ⟨w, hw, wx⟩ := h.2.2.2 A labels.1 R labels.2 x (h.1 A labels.1 x hx)
  exact pn_triple_unique_l hE wx ux ▸ hw

theorem sc_sb_hull_l (hKP : M.Models KP) {X P : M.Domain} (algebra : Sc_algebra_d X)
    (cover : Sc_cover_d X) (hP : M.mem P X) : ∃ T B, M.mem T X ∧ M.mem B X ∧ M.MemberSubset P B ∧ Sb_hull_d T B := by
  obtain ⟨T, hT, trans, sub⟩ := cover P hP
  obtain ⟨Q, hQ, tt⟩ := algebra.product T T hT hT
  obtain ⟨H, hH, tq⟩ := algebra.product T Q hT hQ
  obtain ⟨U, hU, pair⟩ := algebra.pair T H hT hH
  obtain ⟨B, hB, union⟩ := algebra.union U hU
  have bs u : M.mem u B ↔ M.mem u T ∨ ∃ A, M.mem A T ∧ ∃ R, M.mem R T ∧ ∃ x, M.mem x T ∧ Rd_triple_d u A R x := by
    constructor
    · intro hu
      obtain ⟨D, hd, hu⟩ := (union u).mp hu
      rcases (pair D).mp hd with rfl | rfl
      · exact Or.inl hu
      · obtain ⟨A, ha, q, hq, code⟩ := (tq u).mp hu
        obtain ⟨R, hr, x, hx, tuple⟩ := (tt q).mp hq
        exact Or.inr ⟨A, ha, R, hr, x, hx, q, tuple, code⟩
    · rintro (hu | ⟨A, ha, R, hr, x, hx, q, tuple, code⟩)
      · exact (union u).mpr ⟨T, (pair T).mpr (Or.inl rfl), hu⟩
      · exact (union u).mpr ⟨H, (pair H).mpr (Or.inr rfl), (tq u).mpr ⟨A, ha, q, (tt q).mpr ⟨R, hr, x, hx, tuple⟩, code⟩⟩
  refine ⟨T, B, hT, hB, fun p hp => (bs p).mpr (Or.inl (sub p hp)), trans,
    fun t ht => (bs t).mpr (Or.inl ht), fun u hu => (bs u).mp hu, fun A ha R hr x hx => ?_⟩
  obtain ⟨q, qr⟩ := (kp_pair_l hKP).total R x
  obtain ⟨u, uq⟩ := (kp_pair_l hKP).total A q
  exact ⟨u, (bs u).mpr (Or.inr ⟨A, ha, R, hr, x, hx, q, qr, uq⟩), q, qr, uq⟩

/-- 全相对公式在已有界上给出源内无枝关系；背景良基性由实际枝反射保证。 -/
theorem sc_sb_relation_l (hZF : M.Models ZF) {ω c X R B : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hωX : M.mem ω X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R) (hB : M.mem B X) :
    ∃ Q, M.mem Q X ∧ M.IsSetRelationOn (kp_pair_l (ZF.modelsKP hZF)) Q B ∧
      ∀ u v, Rd_entry_d u v Q ↔ M.mem u B ∧ M.mem v B ∧ Sb_bad_d ω X u v := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ne : Nonempty {x // M.mem x X} := ⟨⟨ω, hωX⟩⟩
  let φ : BinarySchema 0 := { body := sb_bad_m, freeClosed := sb_bad_closed_l }
  let ρ : Env (rt_model_l X ne) 0 := ⟨Fin.elim0, fun _ => ⟨ω, hωX⟩⟩
  obtain ⟨Q, hQ, rel, spec⟩ := sc_relation_relative_l hZF hω hX hm theory ne φ ρ hB
  have read (u v : (rt_model_l X ne).Domain) : φ.denote ρ u v ↔ Sb_bad_d ω X u.val v.val :=
    (smem_formula_l I hm ne sb_bad_m ((ρ.push u).push v)).trans (sb_bad_sat_l hZF hω hX hωX hm _)
  refine ⟨Q, hQ, rel, fun u v => ⟨fun huv => ?_, fun ⟨hu, hv, edge⟩ => ?_⟩⟩
  · have bounds := rel.2 u v huv
    exact ⟨bounds.1, bounds.2, (read ⟨u, hX B hB u bounds.1⟩ ⟨v, hX B hB v bounds.2⟩).mp
      ((spec ⟨u, hX B hB u bounds.1⟩ ⟨v, hX B hB v bounds.2⟩).mp huv).2.2⟩
  · exact (spec ⟨u, hX B hB u hu⟩ ⟨v, hX B hB v hv⟩).mpr ⟨hu, hv,
      (read ⟨u, hX B hB u hu⟩ ⟨v, hX B hB v hv⟩).mpr edge⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 枝反射沿完整初等图回拉

先把外部下降链映入目标，由目标反射取得内部分支，再反射一个 Δ₀ 存在句。
此方向不需要共同纤维，也不需要额外选择公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem Sc_branch_d.pull_l {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hωX : M.mem ω X)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (branches : Sc_branch_d ω Y) : Sc_branch_d ω X := by
  intro A P hA hP ⟨f, hf, hd⟩
  obtain ⟨B, hB, hAB⟩ := hj.1.1.2.2 A hA
  obtain ⟨Q, hQ, hPQ⟩ := hj.1.1.2.2 P hP
  have ff := fn0_function_l (ZF.modelsKP hZF) (hf.mono_target_l (hX A hA))
  obtain ⟨g, hg, comp⟩ := ZF.exists_compositionFunction hZF I ff hj.1.1
  have gf : Fn0_d ω B g := (fn0_of_function_l (ZF.modelsKP hZF) hg).retarget_l (fun i y hiy => by
    obtain ⟨_, x, hix, hxy⟩ := (comp i y).mp hiy
    exact ((hn.2 y B).mp ((hj.relation_l I hZF hω hm.1 hn.1 hxy hAB).mp
      ((hm.2 x A).mpr ⟨hj.1.1.input_mem_of_pairMember hxy, hA, (hf.bound_l hix).2⟩))).2.2)
  have gd : Wf_desc_d Q g := by
    intro i m x y hmi hix hmy
    obtain ⟨_, a, hia, hax⟩ := (comp i x).mp hix
    obtain ⟨_, b, hmb, hby⟩ := (comp m y).mp hmy
    exact (hj.entry_l hZF hω hX hY hm hn hby hax hPQ).mp (hd i m a b hmi hia hmb)
  obtain ⟨g', hg', gg⟩ := branches B Q hB hQ ⟨g, gf, gd⟩
  have tr := hj.exists_delta_l hZF hω hX hY hm hn (n := 3)
    (sb_chain_m (.bound 3) (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (sb_chain_delta_l ..)
    ⟨Fin.cases P (Fin.cases A (fun _ => ω)), fun _ => A⟩
    ⟨Fin.cases Q (Fin.cases B (fun _ => ω)), fun _ => B⟩
    (Fin.cases hPQ (Fin.cases hAB (fun _ => hj.omega_l I hZF hω hX hY hm hn hωX)))
  obtain ⟨f', hf', hs⟩ := tr.mpr ⟨g', hg', (sb_chain_sat_l hZF.1 ..).mpr gg⟩
  exact ⟨f', hf', (sb_chain_sat_l hZF.1 ..).mp hs⟩

omit hZF in
/-- 极限相对秩段中的枝只增加有限层秩；此处不要求正则性。 -/
theorem Sc_branch_d.rank_l {ω Z α V : M.Domain} (branches : Sc_branch_d ω Z)
    (hZ : M.TransitiveSet Z) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hωV : M.mem ω V) : Sc_branch_d ω V := by
  intro A R hA hR branch
  obtain ⟨f, hf, fn, desc⟩ := branches A R (hZ V hV A hA) (hZ V hV R hR) branch
  exact ⟨f, rank.relation_mem_l hZ hV hα hωV hA hf (fun p hp => fn.1 p hp), fn, desc⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系对背景内部 ω 序列的闭性

每个证书保留一张实际自然数坐标图，并把背景序列实现为原关系中的函数对象。
有界闭性只量化取值于一个内部集合的序列。坐标唯一性保证递归可以换用同一自然数层的
实际图；传递隶属实例再把对象函数读回原函数图。这些外部闭性不由初等性推出。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Sc_omega_closed_d (ω X R : M.Domain) : Prop := ∃ w z,
  Rr_layer_d I ω X R w z ∧ ∀ f, Fn0_d ω X f →
    ∃ F, Rf_fun_d I X R w F ∧ Rc_graph_d I X R z F f

def Sc_bounded_omega_closed_d (ω X R : M.Domain) : Prop := ∃ w z,
  Rr_layer_d I ω X R w z ∧ ∀ A f, M.mem A X → Fn0_d ω X f →
    (∀ n x, Rd_entry_d n x f → M.PairMember I x A R) →
      ∃ F, Rf_fun_d I X R w F ∧ Rc_graph_d I X R z F f

def sc_omega_closed_m {d} (ω X R : Term d) : Formula 1 d := set[d] ⟪∃ w z,
  ⌜rr_layer_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, w, z) ∧
  (∀ f, ⌜fn0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, f) → ∃ F,
    ⌜rf_fun_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, w, F) ∧
    ⌜rc_graph_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, z, F, f))⟫
derive_free_closed sc_omega_closed_m

def sc_bounded_omega_closed_m {d} (ω X R : Term d) : Formula 1 d := set[d] ⟪∃ w z,
  ⌜rr_layer_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, w, z) ∧
  (∀ A ∈ ⌜X⌝ₛ, ∀ f, ⌜fn0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, f) →
    (∀ n x, ⌜rd_entry0_m⌝ₚ(n, x, f) → ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, A, ⌜R⌝ₛ)) →
    ∃ F, ⌜rf_fun_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, w, F) ∧
      ⌜rc_graph_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, z, F, f))⟫
derive_free_closed sc_bounded_omega_closed_m

theorem sc_omega_closed_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R : Term d) :
    Formula.satisfies ρ (sc_omega_closed_m ω X R) ↔ Sc_omega_closed_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) := by
  simp only [sc_omega_closed_m, Sc_omega_closed_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rr_layer_sat_l I hE, fn0_sat_l hE, rf_fun_sat_l I, rc_graph_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem sc_bounded_omega_closed_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R : Term d) :
    Formula.satisfies ρ (sc_bounded_omega_closed_m ω X R) ↔
      Sc_bounded_omega_closed_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) := by
  simp only [sc_bounded_omega_closed_m, Sc_bounded_omega_closed_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, rr_layer_sat_l I hE, fn0_sat_l hE, rf_fun_sat_l I, rc_graph_sat_l I hE,
    rd_entry0_sat_l hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  exact exists_congr fun w => exists_congr fun z => and_congr_right fun _ =>
    ⟨fun h A f hA => h A hA f, fun h A hA f => h A f hA⟩

theorem Sc_omega_closed_d.at_l (hKP : M.Models KP) {ω X R w z : M.Domain}
    (hω : M.IsOmega ω) (ext : Rf_ext_d I X R) (closed : Sc_omega_closed_d I ω X R)
    (numbers : Rr_layer_d I ω X R w z) : ∀ f, Fn0_d ω X f →
      ∃ F, Rf_fun_d I X R w F ∧ Rc_graph_d I X R z F f := by
  obtain ⟨v, t, old, lift⟩ := closed
  obtain ⟨rfl, rfl⟩ := old.omega_unique_l I hKP hω numbers ext
  exact lift

theorem Sc_bounded_omega_closed_d.at_l (hKP : M.Models KP) {ω X R w z : M.Domain}
    (hω : M.IsOmega ω) (ext : Rf_ext_d I X R) (closed : Sc_bounded_omega_closed_d I ω X R)
    (numbers : Rr_layer_d I ω X R w z) : ∀ A f, M.mem A X → Fn0_d ω X f →
      (∀ n x, Rd_entry_d n x f → M.PairMember I x A R) →
        ∃ F, Rf_fun_d I X R w F ∧ Rc_graph_d I X R z F f := by
  obtain ⟨v, t, old, lift⟩ := closed
  obtain ⟨rfl, rfl⟩ := old.omega_unique_l I hKP hω numbers ext
  exact lift

theorem Sc_omega_closed_d.bounded_l {ω X R : M.Domain}
    (closed : Sc_omega_closed_d I ω X R) : Sc_bounded_omega_closed_d I ω X R := by
  obtain ⟨w, z, numbers, lift⟩ := closed
  exact ⟨w, z, numbers, fun _ f _ ff _ => lift f ff⟩

private theorem sc_omega_read_l (hE : Extensional M) {ω c X R z f F : M.Domain}
    (hX : M.TransitiveSet X) (model : Smem_d I c X R) (hw : M.mem ω X)
    (id : ∀ n x, Rd_entry_d n x z ↔ M.mem n ω ∧ n = x)
    (ff : Fn0_d ω X f) (fn : Rf_fun_d I X R ω F) (graph : Rc_graph_d I X R z F f) : Sfun_d X ω f := by
  obtain ⟨hF, B, hB, fn⟩ := (rf_fun_mem_l I hE hX model hw).mp fn
  have eq := ff.ext_l hE (fn.mono_target_l (hX B hB)) (fun n hn => by
    obtain ⟨x, _, hnx⟩ := ff.2.1 n hn
    exact ⟨x, hnx, (rf_val_mem_l I hE hX model hF).mp
      ((graph n n x ((id n n).mpr ⟨hn, rfl⟩)).mp hnx)⟩)
  exact eq.symm ▸ (show Sfun_d X ω F from ⟨hF, B, hB, fn⟩)

variable (hKP : M.Models KP)
local notation "Kp" => kp_pair_l hKP

private theorem sc_omega_identity_l {ω c X R : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (model : Smem_d Kp c X R) (hw : M.mem ω X) :
    ∃ z, Rr_layer_d Kp ω X R ω z ∧ ∀ n x, Rd_entry_d n x z ↔ M.mem n ω ∧ n = x := by
  obtain ⟨z, fz, graph⟩ := fn0_identity_l hKP ω
  have trans := hω.transitive hKP
  have fn := (fn0_function_l hKP fz).mono_target_l Kp (hX ω hw)
  refine ⟨z, ⟨trans, hw, ⟨fn, fun x y b hx hy =>
    ((graph x b).mp hx).2.trans ((graph y b).mp hy).2.symm⟩, ?_, ?_⟩, graph⟩
  · intro x
    apply (model.2 x ω).trans
    exact ⟨fun h => ⟨x, h.2.2, (graph x x).mpr ⟨h.2.2, rfl⟩⟩,
      fun ⟨n, hn, hx⟩ => ((graph n x).mp hx).2 ▸ ⟨hX ω hw n hn, hw, hn⟩⟩
  · intro n x hnx y
    obtain ⟨hn, rfl⟩ := (graph n x).mp hnx
    apply (model.2 y n).trans
    exact ⟨fun h => ⟨y, h.2.2, (graph y y).mpr ⟨trans n hn y h.2.2, rfl⟩⟩,
      fun ⟨m, hm, hmy⟩ => ((graph m y).mp hmy).2 ▸ ⟨hX ω hw m (trans n hn m hm), hX ω hw n hn, hm⟩⟩

/-- 隶属实例回收同一函数及其源内值域，不增加源模型公理。 -/
theorem sc_omega_closed_mem_l {ω c X R : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (model : Smem_d Kp c X R) (hw : M.mem ω X) :
    Sc_omega_closed_d Kp ω X R ↔ ∀ f, Fn0_d ω X f → Sfun_d X ω f := by
  obtain ⟨z, numbers, id⟩ := sc_omega_identity_l hKP hω hX model hw
  constructor
  · intro closed f ff
    obtain ⟨F, fn, graph⟩ := closed.at_l Kp hKP hω (rf_ext_mem_l Kp hKP.1 hX model) numbers f ff
    exact sc_omega_read_l Kp hKP.1 hX model hw id ff fn graph
  · intro closed
    refine ⟨ω, z, numbers, fun f ff => ?_⟩
    have own := closed f ff
    refine ⟨f, (rf_fun_mem_l Kp hKP.1 hX model hw).mpr own, ?_⟩
    intro n x y hnx
    obtain ⟨_, rfl⟩ := (id n x).mp hnx
    exact (rf_val_mem_l Kp hKP.1 hX model own.1).symm

theorem sc_bounded_omega_closed_mem_l {ω c X R : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (model : Smem_d Kp c X R) (hw : M.mem ω X) :
    Sc_bounded_omega_closed_d Kp ω X R ↔ ∀ A, M.mem A X → ∀ f, Fn0_d ω A f → M.mem f X := by
  obtain ⟨z, numbers, id⟩ := sc_omega_identity_l hKP hω hX model hw
  constructor
  · intro closed A hA f ff
    have fx := ff.mono_target_l (hX A hA)
    obtain ⟨F, fn, graph⟩ := closed.at_l Kp hKP hω (rf_ext_mem_l Kp hKP.1 hX model) numbers A f hA fx
      (fun _ x hnx => (model.2 x A).mpr ⟨(fx.bound_l hnx).2, hA, (ff.bound_l hnx).2⟩)
    exact (sc_omega_read_l Kp hKP.1 hX model hw id fx fn graph).1
  · intro closed
    refine ⟨ω, z, numbers, fun A f hA ff bound => ?_⟩
    have fa := ff.retarget_l (fun n x hnx => ((model.2 x A).mp (bound n x hnx)).2.2)
    have hf := closed A hA f fa
    refine ⟨f, (rf_fun_mem_l Kp hKP.1 hX model hw).mpr ⟨hf, A, hA, fa⟩, ?_⟩
    intro n x y hnx
    obtain ⟨_, rfl⟩ := (id n x).mp hnx
    exact (rf_val_mem_l Kp hKP.1 hX model hf).symm

theorem Sc_bounded_omega_closed_d.branch_l {ω c X R : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (model : Smem_d Kp c X R) (hw : M.mem ω X)
    (closed : Sc_bounded_omega_closed_d Kp ω X R) : Sc_branch_d ω X :=
  fun A _ hA _ ⟨f, hf, desc⟩ =>
    ⟨f, (sc_bounded_omega_closed_mem_l hKP hω hX model hw).mp closed A hA f hf, hf, desc⟩

theorem Sc_bounded_omega_closed_d.rank_l {ω c X R α V d S : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (mx : Smem_d Kp c X R) (hV : M.mem V X) (rank : Vr_d X α V)
    (hα : M.IsLimitOrdinal α) (hw : M.mem ω V) (mv : Smem_d Kp d V S)
    (closed : Sc_bounded_omega_closed_d Kp ω X R) : Sc_bounded_omega_closed_d Kp ω V S := by
  apply (sc_bounded_omega_closed_mem_l hKP hω (rank.transitive_l hX hV) mv hw).mpr
  intro A hA f hf
  have own := (sc_bounded_omega_closed_mem_l hKP hω hX mx (hX V hV ω hw)).mp closed A (hX V hV A hA) f hf
  exact rank.relation_mem_l hX hV hα hw hA own hf.1

/-- 极限秩层对有界值域序列封闭；实际自然数图在 KP 中构造。 -/
theorem sc_v_bounded_omega_closed_l {ω δ V c R : M.Domain} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hV : V_d Kp δ V) (hw : M.mem ω V) (model : Smem_d Kp c V R) :
    Sc_bounded_omega_closed_d Kp ω V R := by
  apply (sc_bounded_omega_closed_mem_l hKP hω (v_transitive_l Kp hV) model hw).mpr
  intro A hA f hf
  obtain ⟨B, hB, wb, ab⟩ := v_joint_bound_l Kp hV hw hA
  exact v_relation_mem_l Kp hV hδ hB (fun p hp => by
    obtain ⟨x, hx, y, hy, pair⟩ := hf.1 p hp
    exact ⟨x, wb x hx, y, ab y hy, pair⟩)

theorem sc_v_omega_closed_l (hZF : M.Models ZF) {ω δ ν V c R : M.Domain} (hω : M.IsOmega ω)
    (cf : M.IsCofinality (kp_pair_l (ZF.modelsKP hZF)) ν δ) (hw : M.mem ω ν)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ V) (hωV : M.mem ω V)
    (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c V R) : Sc_omega_closed_d (kp_pair_l (ZF.modelsKP hZF)) ω V R := by
  let J := kp_pair_l (ZF.modelsKP hZF)
  apply (sc_omega_closed_mem_l (ZF.modelsKP hZF) hω (v_transitive_l J hV) model hωV).mpr
  obtain ⟨i, hi⟩ := ZF.exists_identityBijection hZF J ω
  intro f hf
  obtain ⟨B, hB, fn, own⟩ := ZF.v_small_function_l hZF cf hw ⟨i, hi.1⟩ hωV hV (fn0_function_l (ZF.modelsKP hZF) hf)
  exact ⟨own, B, hB, fn0_of_function_l (ZF.modelsKP hZF) fn⟩

end YesMetaZFC.SetTheory.Internal
