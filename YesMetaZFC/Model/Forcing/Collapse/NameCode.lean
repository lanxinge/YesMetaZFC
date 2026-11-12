import YesMetaZFC.Model.Forcing.Functions.Generic
import YesMetaZFC.Model.Forcing.Truth.Definability
import YesMetaZFC.Model.Forcing.Extension.Choice
import YesMetaZFC.SetTheory.Descriptive.Coding.Prefix
import YesMetaZFC.SetTheory.Card.FiniteSequenceEnd
import YesMetaZFC.SetTheory.FunctionRetraction
import YesMetaZFC.Model.Forcing.Order.ProductRight
import YesMetaZFC.Model.Forcing.Extension.FunctionNames
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.Model.Forcing.Extension.DenseFamily
import YesMetaZFC.Model.Forcing.Check.Order
import YesMetaZFC.Model.Forcing.Embedding.Rank
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.Forcing.Check.SupportBound
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.SetTheory.CumulativeFinite
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable

/-! # 有限初段条件的可数坍缩

条件为 X 值内部有限序列，顺序为反向包含。逐坐标与逐值稠密集实际给出
扩张内 ω 到旧 X 的满射，并保留每条泛型图边的原条件来源。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_collapse_order_l {ω : M.Domain} (hw : M.IsOmega ω) (X : M.Domain) :
    ∃ F R, Fseq_space_d I ω X F ∧ Cond_order_d M F R F ∧
      (∀ p q, Entry_d M p q R ↔ M.mem p F ∧ M.mem q F ∧ M.MemberSubset q p) := by
  obtain ⟨F, space⟩ := ZF.fseq_space_exists_l I hZF hw X
  obtain ⟨R, order, base, _⟩ := subset_order_l M hZF F
  exact ⟨F, R, space, base, order⟩

variable {ω X F R : M.Domain} {G : M.Domain → Prop}
  (hw : M.IsOmega ω)
  (space : Fseq_space_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω X F)
  (order : ∀ p q, Entry_d M p q R ↔ M.mem p F ∧ M.mem q F ∧ M.MemberSubset q p)
  (generic : Generic_d M F R F G)
include hw space order generic

omit generic in
theorem fseq_input_extend_l (inh : ∃ x, M.mem x X) {i p : M.Domain} (hi : M.mem i ω) (hp : M.mem p F) :
    ∃ q, Below_d M F R F q p ∧ ∃ y, Entry_d M i y q := by
  classical
  obtain ⟨n, hn, fn⟩ := (space p).mp hp
  by_cases hin : M.mem i n
  · exact ⟨p, subset_below_l hZF order hp hp (fun _ h => h),
      (fn.2.2 i hin).imp fun y hy => hy.2⟩
  · obtain ⟨x, hx⟩ := inh
    obtain ⟨f, ff, cut, _⟩ := ds_extend_l I hZF hw hn fn hx
    obtain ⟨j, succ, hj⟩ := hw.1.2 i hi
    obtain ⟨q, qr⟩ := ZF.exists_restriction hZF I f j
    have fq := qr.isSetFunctionFromTo ff (hw.transitive (ZF.modelsKP hZF) j hj)
    have ni : M.MemberSubset n j := by
      rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn i hi with eq | lt | gt
      · exact fun a ha => (succ a).mpr (Or.inl ((eq a).mp ha))
      · exact fun a ha => (succ a).mpr (Or.inl ((hw.members_areOrdinals (ZF.modelsKP hZF) i hi).transitive n lt a ha))
      · exact (hin gt).elim
    exact ⟨q, subset_below_l hZF order hp ((space q).mpr ⟨j, hj, fq⟩)
      (ds_prefix_mono_l I fn fq.1 cut qr ni), (fq.2.2 i succ.predecessor_mem).imp fun y hy => hy.2⟩

omit generic in
theorem fseq_output_extend_l {x p : M.Domain} (hx : M.mem x X) (hp : M.mem p F) :
    ∃ q, Below_d M F R F q p ∧ ∃ i, Entry_d M i x q := by
  obtain ⟨n, hn, fn⟩ := (space p).mp hp
  obtain ⟨m, q, hm, fq, endt⟩ := ZF.fseq_end_exists_l I hZF hw hn fn hx
  obtain ⟨m', n', decomp⟩ := endt
  have eq := decomp.prefix_sequence.2.2.2.eq hZF.1 fn.2.1
  subst n'
  exact ⟨q, subset_below_l hZF order hp ((space q).mpr ⟨m, hm, fq⟩)
    (Fseq_end_d.subset_l I ⟨m', n, decomp⟩), n, decomp.last_value⟩

theorem fseq_generic_input_l (inh : ∃ x, M.mem x X) {i : M.Domain} (hi : M.mem i ω) :
    ∃ p, G p ∧ ∃ y, Entry_d M i y p := by
  obtain ⟨p,hp⟩ := generic.inhabited
  let φ : UnarySchema 1 := { body := .existsE (entry_m (.bound 2) .newest (.bound 1)) }
  let ρ : Env M 1 := ⟨fun _ => i,fun _ => i⟩
  have sat p : φ.denote ρ p ↔ ∃ y, Entry_d M i y p := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,entry_sat_l M hZF.1]; rfl
  exact generic_pick_l hZF generic ⟨1,φ,ρ,sat⟩ hp (fun _ hq => fseq_input_extend_l hZF hw space order inh hi hq.1)

theorem fseq_generic_output_l {x : M.Domain} (hx : M.mem x X) : ∃ p, G p ∧ ∃ i, Entry_d M i x p := by
  obtain ⟨p,hp⟩ := generic.inhabited
  let φ : UnarySchema 1 := { body := .existsE (entry_m .newest (.bound 2) (.bound 1)) }
  let ρ : Env M 1 := ⟨fun _ => x,fun _ => x⟩
  have sat p : φ.denote ρ p ↔ ∃ i, Entry_d M i x p := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,entry_sat_l M hZF.1]; rfl
  exact generic_pick_l hZF generic ⟨1,φ,ρ,sat⟩ hp (fun _ hq => fseq_output_extend_l hZF hw space order hx hq.1)

local notation "N" => extension_l M hZF F R F G

theorem fseq_generic_surjection_l (O : Cond_order_d M F R F) (inh : ∃ x, M.mem x X)
    {b : M.Domain} (hb : G b) (e : M.Domain → (N).Domain) (hi : Function.Injective e)
    (he : ∀ a y, (N).mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
    (hv : ∀ a t, Check_d M b a t → Qval_d M F R F G t (e a)) :
    let J := kpair_interpretation_l N (extension_ext_l O hZF generic) (internal_pair_l O hZF generic)
    ∃ g, (N).IsSetFunctionFromTo J g (e ω) (e X) ∧ (N).IsSetSurjectiveOnto J g (e ω) (e X) ∧
      ∀ x y, Entry_d N x y g ↔ ∃ p, G p ∧ ∃ a c, Entry_d M a c p ∧ e a = x ∧ e c = y := by
  have pf {p} (hp : G p) : Pfn_d I ω X p := by
    obtain ⟨n, hn, fn⟩ := (space p).mp (generic.proper p hp).1
    exact ⟨fn.1, fun i x ix => ⟨hw.transitive (ZF.modelsKP hZF) n hn i (fn.input_mem_of_pairMember ix), fn.output_mem_of_pairMember ix⟩⟩
  obtain ⟨g, fn, graph⟩ := generic_function_l (hEN := extension_ext_l O hZF generic) (hPN := internal_pair_l O hZF generic)
    O hZF generic hb pf (fun p q h => ((order p q).mp h).2.2)
    (fun _ hi => fseq_generic_input_l hZF hw space order generic inh hi) e hi he hv
  refine ⟨g, fn, ?_, graph⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (he X x).mp hx
  obtain ⟨p, hp, i, ia⟩ := fseq_generic_output_l hZF hw space order generic ha
  exact ⟨e i, (image_member_l e hi he).mpr ((pf hp).2 i a ia).1,
    (graph (e i) (e a)).mpr ⟨p, hp, i, a, ia, rfl, rfl⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 大坍缩扩张中旧小集合的实际枚举

旧集合到被坍缩字母域的单射在扩张中保持。取其带默认值的反向函数，
与实际泛型满射复合，即得到扩张自己的 ω 上的满射；只需 ZF。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_small_enumeration_l {ω δ B R X b : M.Domain} (O : Cond_order_d M B R B)
    (hw : M.IsOmega ω) (space : Fseq_space_d I ω δ B)
    (order : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    (bound : M.CardinalLessOrEqual I X δ) (inh : ∃ x, M.mem x X)
    {G : M.Domain → Prop} (generic : Generic_d M B R B G) (hb : G b)
    (j : M.Domain → (extension_l M hZF B R B G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF B R B G).mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M B R B G t (j a)) :
    let N := extension_l M hZF B R B G
    let hN := preserves_zf_l O hZF generic
    let J := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))
    ∃ e, N.IsSetFunctionFromTo J e (j ω) (j X) ∧ N.IsSetSurjectiveOnto J e (j ω) (j X) := by
  let N := extension_l M hZF B R B G
  have hN : N.Models ZF := preserves_zf_l O hZF generic
  let J := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))
  obtain ⟨a,ha⟩ := inh
  obtain ⟨f,ff⟩ := bound
  obtain ⟨d,hd,_⟩ := ff.1.2.2 a ha
  obtain ⟨g,fg,onto,_⟩ := fseq_generic_surjection_l hZF hw space order generic O ⟨d,hd⟩ hb j inj full checks
  have image : N.IsSetInjectionFromTo J (j f) (j X) (j δ) := image_injection_l j inj full ff
  obtain ⟨r,fr,back⟩ := ZF.injection_retract_l J hN image (fun _ hx => hx) ((image_member_l j inj full).mpr ha)
  obtain ⟨e,fe,graph⟩ := ZF.exists_compositionFunction hN J fg fr
  refine ⟨e,fe,fun x hx => ?_⟩
  obtain ⟨d,hd,xd⟩ := image.1.2.2 x hx
  obtain ⟨n,hn,nd⟩ := onto d hd
  exact ⟨n,hn,(graph n x).mpr ⟨hn,d,nd,back x d xd⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 小坍缩与大坍缩的积函数名字族

实际构造两个有限序列条件序和积条件序，使用共同空条件作规范名字基点。
全局函数名字族覆盖该积的每个泛型扩张中的全部 ω→X 函数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_product_names_l {ω X : M.Domain} (hw : M.IsOmega ω)
    (inh : ∃ x, M.mem x X) (κ δ : M.Domain) :
    ∃ Q T P U C R b c t w Z a f s W A,
      Fseq_space_d I ω κ Q ∧ Fseq_space_d I ω δ P ∧
      (∀ q r, Entry_d M q r T ↔ M.mem q Q ∧ M.mem r Q ∧ M.MemberSubset r q) ∧
      (∀ p r, Entry_d M p r U ↔ M.mem p P ∧ M.mem r P ∧ M.MemberSubset r p) ∧
      Cond_order_d M Q T Q ∧ Cond_order_d M P U P ∧ Prod_d hZF Q T P U C R ∧
      ∃ K : Cond_order_d M C R C, (∀ x, ¬ M.mem x b) ∧ KPair_d M c b b ∧ M.mem c C ∧
      (∀ p, M.mem p C → Entry_d M p c R) ∧
      Check_d M c ω t ∧ Check_d M c X w ∧ M.IsCartesianProduct I Z ω X ∧ Check_d M c Z a ∧
      M.IsSetFunctionFromTo I f ω X ∧ Check_d M c f s ∧ Name_pool_d M C a s W ∧ M.mem s A ∧
      (∀ v, M.mem v A ↔ M.mem v W ∧ ∀ p, M.mem p C → p ≠ C →
        Forces_d M C R C fn_body_m (fn_env_l t w v) p) ∧
      ∀ G (generic : Generic_d M C R C G),
        ∀ d x y : (extension_l M hZF C R C G).Domain,
          Qval_d M C R C G t d → Qval_d M C R C G w x →
          (extension_l M hZF C R C G).IsSetFunctionFromTo
            (kpair_interpretation_l _ (extension_ext_l K hZF generic)
              (internal_pair_l K hZF generic)) y d x →
          ∃ v, M.mem v A ∧ Qval_d M C R C G v y := by
  obtain ⟨Q,T,qs,O,qt⟩ := fseq_collapse_order_l hZF hw κ
  obtain ⟨P,U,ps,L,pt⟩ := fseq_collapse_order_l hZF hw δ
  obtain ⟨C,R,product,K⟩ := product_order_l hZF O L
  obtain ⟨b,empty,hb⟩ := hw.1.1
  have bQ := (qs b).mpr ⟨b,hb,ds_empty_fun_l I empty⟩
  have bP := (ps b).mpr ⟨b,hb,ds_empty_fun_l I empty⟩
  obtain ⟨c,cc⟩ := (I).total b b
  obtain ⟨hc,top⟩ := product.top_l hZF bQ bP
    (fun q hq => (qt q b).mpr ⟨hq,bQ,fun x hx => (empty x hx).elim⟩)
    (fun p hp => (pt p b).mpr ⟨hp,bP,fun x hx => (empty x hx).elim⟩) cc
  obtain ⟨t,w,Z,a,f,s,W,A,ht,hw',hz,ha,hf,hs,pool,chosen,family,cover⟩ :=
    function_names_l hZF K hc top inh (D := ω)
  exact ⟨Q,T,P,U,C,R,b,c,t,w,Z,a,f,s,W,A,qs,ps,qt,pt,O,L,product,K,
    empty,cc,hc,top,ht,hw',hz,ha,hf,hs,pool,chosen,family,cover⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 小坍缩之上的大坍缩稠密集名称

从两个实际内部有限序列条件域出发，小坍缩的空条件自动给出规范名称基点。
大坍缩的条件域和序关系的规范名称满足预序力迫，故上层名称库覆盖小泛型
扩张中大坍缩的全部稠密集。构造只需 ZF，不另交名称覆盖或力迫正确性假设。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_dense_names_l {ω κ B R : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω κ B) (O : Cond_order_d M B R B)
    (order : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    (δ : M.Domain) :
    ∃ F S b A T W D, Fseq_space_d I ω δ F ∧ Cond_order_d M F S F ∧
      (∀ p q, Entry_d M p q S ↔ M.mem p F ∧ M.mem q F ∧ M.MemberSubset q p) ∧
      (∀ x, ¬ M.mem x b) ∧ M.mem b B ∧ Check_d M b F A ∧ Check_d M b S T ∧ Name_pool_d M B A A W ∧
      (∀ s, M.mem s D ↔ M.mem s W ∧ ∀ p, M.mem p B → p ≠ B →
        Forces_d M B R B dn_s.body ((ord_env_l M A T).push s) p) ∧
      ∀ U, Generic_d M B R B U → ∀ C V K : (extension_l M hZF B R B U).Domain,
        Qval_d M B R B U A C → Qval_d M B R B U T V →
        Dense_set_d (extension_l M hZF B R B U) C V C K →
        ∃ s, M.mem s D ∧ Qval_d M B R B U s K := by
  obtain ⟨F, S, fs, L, ord⟩ := fseq_collapse_order_l hZF hw δ
  obtain ⟨b, empty, hbω⟩ := hw.1.1
  have hb := (space b).mpr ⟨b, hbω, ds_empty_fun_l I empty⟩
  have top p (hp : M.mem p B) := (order p b).mpr ⟨hp, hb, fun a ha => (empty a ha).elim⟩
  obtain ⟨A, hA, hnA, _⟩ := zf_check_l M hZF hb F
  obtain ⟨T, hT, hnT, _⟩ := zf_check_l M hZF hb S
  obtain ⟨W, D, pool, spec, cover⟩ := dense_names_l O hZF hnA hnT (fun p hp hz =>
    check_preord_force_l O hZF hb hA hT ⟨L.refl, L.trans⟩ ⟨hp, hz, top p hp⟩)
  exact ⟨F, S, b, A, T, W, D, fs, L, ord, empty, hb, hA, hT, pool, spec, cover⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 7.22 的小坍缩提升在实际迭代秩段上的实例

源中的全部内部有限 κ 列作为有界关系族进入共同的低极限秩段。
因此无需另交条件覆盖、稠密集覆盖或目标泛型性；它们都由原秩证书恢复。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smem_d.fseq_rank_l {c X R μ V : M.Domain} (xt : M.TransitiveSet X)
    (mx : Smem_d I c X R) (hV : M.mem V X) (rank : Vr_d X μ V) (limit : M.IsLimitOrdinal μ)
    (hA : (smdl_structure_l I (R := R) mx.1.2.1).Models ZF)
    (ω κ P : (smdl_structure_l I (R := R) mx.1.2.1).Domain) (hw : M.IsOmega ω.val)
    (hωV : M.mem ω.val V) (hκV : M.mem κ.val V)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hA)) ω κ P) : M.mem P.val V := by
  let A := smdl_structure_l I (R := R) mx.1.2.1
  apply rank.relations_mem_l xt hV limit hωV hκV P.property
  intro f hf p hp
  let f' : A.Domain := ⟨f, xt P.val P.property f hf⟩
  obtain ⟨n, hn, fn⟩ := (space f').mp ((mx.2 f P.val).mpr ⟨f'.property, P.property, hf⟩)
  let ρ : Env A 3 := ⟨Fin.cases f' (Fin.cases κ (fun _ => n)), fun _ => n⟩
  have fn' : Fn0_d n.val κ.val f :=
    (fn0_sat_l hZF.1 (@image_env_l A M Subtype.val 3 ρ) (.bound 2) (.bound 1) .newest).mp
      ((smem_delta_image_l I mx xt (fn0_delta_l ..) ρ).mp
        ((fn0_sat_l hA.1 ρ (.bound 2) (.bound 1) .newest).mpr (fn0_of_function_l (ZF.modelsKP hA) fn)))
  obtain ⟨i, hi, a, ha, pair⟩ := fn'.1 p hp
  exact ⟨i, hw.transitive (ZF.modelsKP hZF) n.val ((mx.2 n.val ω.val).mp hn).2.2 i hi, a, ha, pair⟩

/-- 原内部有限条件及给定小泛型，自动提升已有初等图并保持同一个滤子。 -/
theorem Smap_d.collapse_lift_l {ω c d X R Y S j μ ν V : M.Domain}
    (hw : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (map : Smap_d I ω c d X Y j)
    (hμ : Rd_entry_d μ ν j) (fixed : ∀ β, M.mem β μ → Rd_entry_d β β j)
    (hVX : M.mem V X) (rx : Vr_d X μ V) (hVY : M.mem V Y) (ry : Vr_d Y μ V)
    (limit : M.IsLimitOrdinal μ) (hωμ : M.mem ω μ)
    (hA : (smdl_structure_l I (R := R) mx.1.2.1).Models ZF)
    (hB : (smdl_structure_l I (R := S) my.1.2.1).Models ZF)
    (w κ P Q : (smdl_structure_l I (R := R) mx.1.2.1).Domain) (hw' : w.val = ω) (hκμ : M.mem κ.val μ)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hA)) w κ P)
    (O : Cond_order_d _ P Q P) {U} (generic : Generic_d _ P Q P U) :
    ∃ e : (smdl_structure_l I (R := R) mx.1.2.1).Domain → (smdl_structure_l I (R := S) my.1.2.1).Domain,
      Pe_d e ∧ (∀ x, Rd_entry_d x.val (e x).val j) ∧
      Generic_d _ (e P) (e Q) (e P) (Em_generic_d e U) ∧
      (∀ q, Em_generic_d e U q ↔ ∃ p, U p ∧ p.val = q.val) ∧
      ∃ f : (extension_l _ hA P Q P U).Domain → (extension_l _ hB (e P) (e Q) (e P) (Em_generic_d e U)).Domain,
        Function.Injective f ∧
        (∀ t x, Qval_d _ P Q P U t x → Qval_d _ (e P) (e Q) (e P) (Em_generic_d e U) (e t) (f x)) ∧
        (∀ {n} (φ : Formula 1 n), φ.FreeClosed → ∀ ρ, Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l f ρ) φ) ∧
        ∀ τ, M.mem τ.val V → ∀ x, Qval_d _ P Q P U τ x → ∀ y,
          (extension_l _ hB (e P) (e Q) (e P) (Em_generic_d e U)).mem y (f x) ↔
            ∃ t, (extension_l _ hA P Q P U).mem t x ∧ f t = y := by
  have low := rx.ordinal_subset_l hZF xt hVX
  have hp := mx.fseq_rank_l hZF xt hVX rx limit hA w κ P (hw'.symm ▸ hw)
    (hw'.symm ▸ low ω hωμ) (low κ.val hκμ) space
  exact map.rank_lift_l hZF hw xt yt mx my hμ fixed hVX rx hVY ry hA hB P Q P hp O generic

end YesMetaZFC.SetTheory.Internal

/-! ## 大坍缩规范名称库的实际幂集编码

每个 δ 字母有限条件属于 Vδ，故 Vδ∪{δ^{<ω}} 是包含条件域的传递容器。
不可达性给出该容器到 δ 的实际单射；规范名称支撑及整个混合库随之编码。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_check_code_l {ω κ δ B F b A W P : M.Domain}
    (hw : M.IsOmega ω) (above : M.mem ω δ) (regular : M.IsRegularCardinal I δ)
    (strong : M.IsStrongLimitCardinal I δ) (small : M.MemberSubset κ δ)
    (conditions : Fseq_space_d I ω κ B) (space : Fseq_space_d I ω δ F)
    (hb : M.mem b B) (check : Check_d M b F A) (pool : Name_pool_d M B A A W)
    (power : M.IsPowerSetOf P δ) : M.CardinalLessOrEqual I W P := by
  have infinite : M.IsInfiniteCardinal I ω δ := ⟨regular.isCardinal,
    ZF.exists_inclusionInjection hZF I (regular.isCardinal.1.transitive ω above)⟩
  obtain ⟨V,rank⟩ := ZF.v_exists_l I hZF regular.isCardinal.1
  have hv := v_transitive_l I rank
  have finite : M.MemberSubset F V := by
    intro s hs
    obtain ⟨n,hn,fn⟩ := (space s).mp hs
    obtain ⟨_,_,_,member⟩ := ZF.v_finite_function_l hZF hw regular.isLimitOrdinal rank
      (ZF.v_ordinal_mem_l I hZF rank above) hn
      (Structure.IsSetFunctionFromTo.mono_target_l I fn (ZF.v_ordinal_subset_l I hZF rank))
    exact member
  obtain ⟨C,insert⟩ := KP.exists_insert (ZF.modelsKP hZF) V F
  have trans : M.TransitiveSet C := by
    intro x hx y hy
    apply (insert y).mpr
    exact Or.inl (((insert x).mp hx).elim (fun hx => hv x hx y hy) (fun eq => finite y (eq ▸ hy)))
  obtain ⟨f,bijection⟩ := ZFC.inaccessible_enumeration_l I hZFC hw above regular strong rank
  obtain ⟨g,inverse,_⟩ := ZF.exists_inverseBijectionWithPairs hZF I bijection
  have count := ZF.infinite_insert_l I hZF hw infinite ⟨g,inverse.1⟩ insert
  have base := ZF.fseq_bound_l I hZF hw infinite (ZF.exists_inclusionInjection hZF I small) conditions
  exact pool.check_code_l hZF check hb hw infinite trans ((insert F).mpr (Or.inr rfl)) count base power

theorem fseq_dense_names_code_l {ω κ δ B R : M.Domain} (hw : M.IsOmega ω)
    (above : M.mem ω δ) (regular : M.IsRegularCardinal I δ) (strong : M.IsStrongLimitCardinal I δ)
    (small : M.MemberSubset κ δ) (space : Fseq_space_d I ω κ B) (O : Cond_order_d M B R B)
    (order : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p) :
    ∃ F S b A T W D P, Fseq_space_d I ω δ F ∧ Cond_order_d M F S F ∧
      (∀ p q, Entry_d M p q S ↔ M.mem p F ∧ M.mem q F ∧ M.MemberSubset q p) ∧
      (∀ x, ¬ M.mem x b) ∧ M.mem b B ∧ Check_d M b F A ∧ Check_d M b S T ∧ Name_pool_d M B A A W ∧
      M.IsPowerSetOf P δ ∧ M.CardinalLessOrEqual I W P ∧ M.CardinalLessOrEqual I D P ∧ M.mem A D ∧
      (∀ s, M.mem s D ↔ M.mem s W ∧ ∀ p, M.mem p B → p ≠ B →
        Forces_d M B R B dn_s.body ((ord_env_l M A T).push s) p) ∧
      ∀ U, Generic_d M B R B U → ∀ C V K : (extension_l M hZF B R B U).Domain,
        Qval_d M B R B U A C → Qval_d M B R B U T V →
        Dense_set_d (extension_l M hZF B R B U) C V C K →
        ∃ s, M.mem s D ∧ Qval_d M B R B U s K := by
  obtain ⟨F,S,b,A,T,W,D,finite,ord,orders,empty,hb,check,relation,pool,spec,cover⟩ :=
    fseq_dense_names_l hZF hw space O order δ
  obtain ⟨P,power⟩ := ZF.exists_powerSet hZF δ
  obtain ⟨f,fn⟩ := fseq_check_code_l hZFC hw above regular strong small space finite hb check pool power
  obtain ⟨g,sub⟩ := ZF.exists_inclusionInjection hZF I (fun s hs => ((spec s).mp hs).1)
  -- 全条件域的规范名称是库中实际选定元素，可直接满足第一辅助域的非空要求。
  have chosen : M.mem A D := (spec A).mpr ⟨pool.left,fun p hp hz =>
    dense_full_force_l O hZF (check_name_l M (check_range_l M hZF) hb check)
      (check_name_l M (check_range_l M hZF) hb relation) hp hz
      (check_preord_force_l O hZF hb check relation ⟨ord.refl,ord.trans⟩
        ⟨hp,hz,(order p b).mpr ⟨hp,hb,fun x hx => (empty x hx).elim⟩⟩)⟩
  exact ⟨F,S,b,A,T,W,D,P,finite,ord,orders,empty,hb,check,relation,pool,power,⟨f,fn⟩,
    ZF.exists_compositionInjection hZF I sub fn,chosen,spec,cover⟩

end YesMetaZFC.Model.Forcing.Internal
