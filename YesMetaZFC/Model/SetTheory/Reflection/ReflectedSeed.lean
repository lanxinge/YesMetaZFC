import YesMetaZFC.Model.SetTheory.Embedding.ElementaryTrace
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax
import YesMetaZFC.SetTheory.Collapse.EmbeddingFixed
import YesMetaZFC.Model.SetTheory.LevyReflection
import YesMetaZFC.SetTheory.Card.FiniteParameters
import YesMetaZFC.SetTheory.Card.CountablePair
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.SetTheory.Source.Theory
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax
import YesMetaZFC.SetTheory.Descriptive.Game.GameWitness
import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.SetTheory.InnerModel.Relative.PayoffQuerySound
import YesMetaZFC.SetTheory.InnerModel.Relative.TruthImage

/-! # 有限反射下固定可数传递种子的测试壳

先在背景反射指定有限公式族，再对真实秩层取可数初等壳并坍塌。
全部种子成员逐点固定；其余有限参数保留实际原像。反坍塌对指定公式
直达背景真值，不要求反射秩层或测试壳满足完整 ZFC。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Rf_hull_d (ω T : M.Domain) (Φ : List Lr_formula) {n} (v : Fin n → M.Domain)
    (α V d S P c R π : M.Domain) : Prop where
  rank : V_d I α V
  limit : M.IsLimitOrdinal α
  reflect : ∀ q ∈ Φ, Lr_reflect_d q.2.val V
  target : Smem_d I d V S
  model : Smem_d I c P R
  transitive : M.TransitiveSet P
  count : M.CardinalLessOrEqual I P ω
  map : Smap_d I ω c d P V π
  seed : M.MemberSubset T P
  fixed : ∀ x, M.mem x T → Rd_entry_d x x π
  params : ∀ i, ∃ x, Rd_entry_d x (v i) π

/-- 极限秩层的配对闭包沿反坍塌反射；不要求测试壳满足 KP。 -/
theorem Rf_hull_d.pairs_l {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
    {n} {v : Fin n → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
    (hw : M.IsOmega ω) :
    ∀ a b : (smdl_structure_l I (R := R) h.model.1.2.1).Domain, ∃ p,
      Pair_d (smdl_structure_l I (R := R) h.model.1.2.1) p a b := by
  intro a b
  obtain ⟨a',ha',aa⟩ := h.map.1.1.2.2 a.val a.property
  obtain ⟨b',hb',bb⟩ := h.map.1.1.2.2 b.val b.property
  obtain ⟨q,hq,pair⟩ := sc_v_pair_l (ZF.modelsKP hZF) h.limit h.rank a' b' ha' hb'
  have tr := h.map.exists_delta_l hZF hw h.transitive (v_transitive_l I h.rank) h.model h.target
    (n := 2) (pair0_m .newest (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs) (pair0_delta_l ..)
    ⟨Fin.cases a.val (fun _ => b.val),fun _ => a.val⟩
    ⟨Fin.cases a' (fun _ => b'),fun _ => a'⟩ (Fin.cases aa (fun _ => bb))
  simp only [pair0_sat_l hZF.1] at tr
  obtain ⟨p,hp,pp⟩ := tr.mpr ⟨q,hq,pair⟩
  refine ⟨⟨p,hp⟩,fun x => ?_⟩
  exact (smem_member_l I h.model.1 h.model.2 x ⟨p,hp⟩).trans
    ((pp x.val).trans ⟨fun e => e.elim (fun e => Or.inl (Subtype.ext e))
      (fun e => Or.inr (Subtype.ext e)),fun e => e.elim (fun e => Or.inl (congrArg Subtype.val e))
        (fun e => Or.inr (congrArg Subtype.val e))⟩)

theorem Rf_hull_d.formula_l {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
    {n} {v : Fin n → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
    (hw : M.IsOmega ω) {m} (φ : Formula 1 m) (hc : φ.FreeClosed) (mem : (⟨m,φ,hc⟩ : Lr_formula) ∈ Φ)
    (ρ : Env (smdl_structure_l I (R := R) h.model.1.2.1) m) (η : Env M m)
    (images : ∀ i, Rd_entry_d (ρ.bound i).val (η.bound i) π) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  let N := smdl_structure_l I (R := S) h.target.1.2.1
  obtain ⟨z,hz⟩ := h.target.1.2.1
  let θ : Env N m := ⟨fun i => ⟨η.bound i,h.map.1.1.output_mem_of_pairMember (images i)⟩,fun _ => ⟨z,hz⟩⟩
  have tr := smap_source_l I hZF hw h.model.1 h.target.1 h.map φ hc ρ θ images
  have read := lr_rel_decode_l I h.target.1 h.target.2 (v_transitive_l I h.rank) φ hc θ
    (η.push V) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)
  exact tr.trans (read.symm.trans (h.reflect ⟨m,φ,hc⟩ mem η
    (fun i => h.map.1.1.output_mem_of_pairMember (images i))).symm)

omit hZF in
theorem rf_hull_l (hZFC : M.Models ZFC) {ω T : M.Domain} (hw : M.IsOmega ω)
    (trans : M.TransitiveSet T)
    (count : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) T ω)
    (Φ : List Lr_formula) {n} (v : Fin n → M.Domain) :
    ∃ α V d S P c R π, Rf_hull_d (ZFC.models_zf_l hZFC) ω T Φ v α V d S P c R π := by
  let hZF := ZFC.models_zf_l hZFC
  let J := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B,finite,params⟩ := ZF.finite_params_l J hZF hw v
  obtain ⟨A,union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) T B
  have small := ZF.countable_union_two_l J hZF hw count (ZF.finite_countable_l J hZF hw finite) union
  obtain ⟨α,V,rank,limit,hA,reflect⟩ := ZF.lr_finite_l J hZF Φ A
  have vt := v_transitive_l J rank
  obtain ⟨d,S,mdl,rel⟩ := smdl_membership_l J hZF ⟨A,hA⟩
  have target : Smem_d J d V S := ⟨mdl,rel⟩
  obtain ⟨X,d₀,S₀,P,F,π,c,R,_,cover,_,_,pt,collapse,bound,inverse,model,map⟩ :=
    selem_hull_collapse_l hZFC hw vt target (vt A hA) small
  have preimage x (hx : M.mem x A) : ∃ y, Rd_entry_d y x π := by
    obtain ⟨y,_,xy⟩ := collapse.function.2.1 x (cover x hx)
    exact ⟨y,(inverse x y).mpr xy⟩
  have seed x (hx : M.mem x T) := preimage x ((union x).mpr (Or.inl hx))
  obtain ⟨inside,fixed⟩ := mem_embedding_fixed_l hZF pt map.1
    (fun _ _ _ _ hx hy => map.member_l J hZF hw model target hx hy) trans seed
  exact ⟨α,V,d,S,P,c,R,π,rank,limit,reflect,target,model,pt,bound,map,inside,fixed,
    fun i => preimage (v i) ((union (v i)).mpr (Or.inr ((params (v i)).mpr ⟨i,rfl⟩)))⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 反射壳包含全部背景内部有限函数

配对和并集沿反坍塌回收，有限图闭包由背景内部归纳给出。
极限秩层的有限序列空间随后反射到壳内，并识别为真实的完整空间。
这里不把测试壳的有限闭包升级为 KP 或 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
  {n} {v : Fin n → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
  (hw : M.IsOmega ω)
include h hw

theorem Rf_hull_d.pair_mem_l {a b : M.Domain} (ha : M.mem a P) (hb : M.mem b P) :
    ∃ p, M.mem p P ∧ Pair_d M p a b := by
  let N := smdl_structure_l I (R := R) h.model.1.2.1
  obtain ⟨p,pair⟩ := h.pairs_l hZF hw ⟨a,ha⟩ ⟨b,hb⟩
  exact ⟨p.val,p.property,image_pair_l (M := N) (N := M) Subtype.val
    (smem_full_l I h.model h.transitive) pair⟩

theorem Rf_hull_d.union_mem_l {A : M.Domain} (ha : M.mem A P) :
    ∃ U, M.mem U P ∧ M.IsUnionOf U A := by
  obtain ⟨B,hb,ab⟩ := h.map.1.1.2.2 A ha
  obtain ⟨β,W,hβ,rank,sub⟩ := (ZF.v_unfold_l I hZF h.rank B).mp hb
  obtain ⟨U,un⟩ := KP.exists_union (ZF.modelsKP hZF) B
  have hu := v_subset_mem_l I h.rank (ZF.v_mem_l I hZF rank h.rank hβ) (fun x hx =>
    ((un x).mp hx).elim fun y hy => v_transitive_l I rank y (sub y hy.1) x hy.2)
  have tr := h.map.exists_delta_l hZF hw h.transitive (v_transitive_l I h.rank) h.model h.target
    (n := 1) (rd_graph_m .union (.bound 1) (.bound 1) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (rd_graph_delta_l ..)
    ⟨fun _ => A,fun _ => A⟩ ⟨fun _ => B,fun _ => B⟩ (fun _ => ab)
  simp only [rd_graph_sat_l (ZF.modelsKP hZF)] at tr
  exact tr.mpr ⟨U,hu,un⟩

theorem Rf_hull_d.finite_closed_l (hω : M.mem ω P) {A b f : M.Domain}
    (ha : M.MemberSubset A P) (hb : M.mem b ω) (fn : Fn0_d b A f) : M.mem f P :=
  sc_finite_function_l (ZF.modelsKP hZF) hw h.transitive
    (fun _ _ => h.pair_mem_l hZF hw) (fun _ => h.union_mem_l hZF hw) hω ha hb fn

/-- 壳内的序列空间包括全部背景内部有限图，而不只包括已在壳内的图。 -/
theorem Rf_hull_d.fseq_l (hω : M.mem ω P) {A : M.Domain} (ha : M.mem A P) :
    ∃ K, M.mem K P ∧ Fseq_space_d I ω A K := by
  have vt := v_transitive_l I h.rank
  have fixed := h.map.omega_l I hZF hw h.transitive vt h.model h.target hω
  have hωV := h.map.1.1.output_mem_of_pairMember fixed
  have sequences := (sc_sequences_iff_l I hZF hw h.model.1 h.target.1 h.map fixed).mpr
    (sc_v_sequences_l hZF hw h.limit (ZF.v_ordinal_height_l hZF h.rank (hw.isOrdinal (ZF.modelsKP hZF)) hωV)
      h.rank h.target)
  obtain ⟨K,space⟩ := sequences.space_l I ha
  have hk := space.mem_l
  exact ⟨K,hk,(sc_fseq_mem_l I (ZF.modelsKP hZF) hw h.transitive h.model hω ha hk
    (fun _ _ => h.pair_mem_l hZF hw) (fun _ => h.union_mem_l hZF hw)).mp space⟩

/-- 一份已有有限序列空间的反坍塌像仍包含所有目标有限图。 -/
theorem Rf_hull_d.fseq_image_l (hω : M.mem ω P) {A A' K K' : M.Domain}
    (aa : Rd_entry_d A A' π) (kk : Rd_entry_d K K' π) (space : Fseq_space_d I ω A K) :
    Fseq_space_d I ω A' K' := by
  have vt := v_transitive_l I h.rank
  have fixed := h.map.omega_l I hZF hw h.transitive vt h.model h.target hω
  let φ : Formula 1 4 := .iff (.mem .newest (.bound 1))
    (Formula.existsMem (.bound 3) (fn0_m .newest (.bound 3) (.bound 1)))
  have tr := h.map.forall_delta_l hZF hw h.transitive vt h.model h.target φ
    (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed])
    (.iff (.mem ..) (.existsMem _ (fn0_delta_l ..)))
    ⟨Fin.cases K (Fin.cases A (fun _ => ω)),fun _ => ω⟩
    ⟨Fin.cases K' (Fin.cases A' (fun _ => ω)),fun _ => ω⟩ (Fin.cases kk (Fin.cases aa (fun _ => fixed)))
  simp only [φ,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,Formula.satisfies_existsMem_iff,
    fn0_sat_l hZF.1] at tr
  have read := tr.mp (fun f _ => (space f).trans (exists_congr fun b => and_congr_right fun _ =>
    ⟨fn0_of_function_l (ZF.modelsKP hZF),fn0_function_l (ZF.modelsKP hZF)⟩))
  intro f
  constructor
  · intro hf
    obtain ⟨b,hb,fn⟩ := (read f (vt K' (h.map.1.1.output_mem_of_pairMember kk) f hf)).mp hf
    exact ⟨b,hb,fn0_function_l (ZF.modelsKP hZF) fn⟩
  · rintro ⟨b,hb,fn⟩
    -- 有限图也受整个 ω×A' 的关系界控制，故属于极限秩层。
    have hf : M.mem f V := by
      obtain ⟨D,hd,wd,ad⟩ := v_joint_bound_l I h.rank (h.map.1.1.output_mem_of_pairMember fixed)
        (h.map.1.1.output_mem_of_pairMember aa)
      exact v_relation_mem_l I h.rank h.limit hd (fun p hp => by
        obtain ⟨x,y,pair⟩ := fn.1.1 p hp
        exact ⟨x,wd x (hw.transitive (ZF.modelsKP hZF) b hb x (fn.input_mem_of_pairMember ⟨p,pair,hp⟩)),
          y,ad y (fn.output_mem_of_pairMember ⟨p,pair,hp⟩),pair⟩)
    exact (read f hf).mpr ⟨b,hb,fn0_of_function_l (ZF.modelsKP hZF) fn⟩

/-- 指定内部有限长度后，同时构造源、像两侧的真实完整赋值空间。 -/
theorem Rf_hull_d.finite_space_l (hω : M.mem ω P) {b A A' : M.Domain}
    (hb : M.mem b ω) (aa : Rd_entry_d A A' π) :
    ∃ E E', M.mem E P ∧ Rd_entry_d E E' π ∧
      M.IsFunctionSpace I E b A ∧ M.IsFunctionSpace I E' b A' := by
  have vt := v_transitive_l I h.rank
  have bb := h.map.natural_l hZF hw h.transitive vt h.model h.target hω b hb
  obtain ⟨K,hk,space⟩ := h.fseq_l hZF hw hω (h.map.1.1.input_mem_of_pairMember aa)
  obtain ⟨K',hk',kk⟩ := h.map.1.1.2.2 K hk
  have space' := h.fseq_image_l hZF hw hω aa kk space
  obtain ⟨D,fd⟩ := ZF.exists_functionSpace hZF I b A'
  have bound := (fv_space_l (ZF.modelsKP hZF) hb space').mpr fd
  have hd := v_subset_mem_l I h.rank hk' bound.1
  let φ : Formula 1 4 := fv_space_m (.bound 1) (.bound 2) (.bound 3) .newest
  let ρ : Env M 3 := ⟨Fin.cases b (Fin.cases A (fun _ => K)),fun _ => K⟩
  let η : Env M 3 := ⟨Fin.cases b (Fin.cases A' (fun _ => K')),fun _ => K'⟩
  have tr := h.map.exists_delta_l hZF hw h.transitive vt h.model h.target φ
    (by simp -implicitDefEqProofs [φ]) (fv_space_delta_l ..) ρ η (Fin.cases bb (Fin.cases aa (fun _ => kk)))
  simp only [φ,fv_space_sat_l hZF.1] at tr
  obtain ⟨E,he,fe⟩ := tr.mpr ⟨D,hd,bound⟩
  obtain ⟨E',_,ee⟩ := h.map.1.1.2.2 E he
  have copied := smap_delta_l I hZF hw h.transitive vt h.model h.target h.map φ
    (by simp -implicitDefEqProofs [φ]) (fv_space_delta_l ..) (ρ.push E) (η.push E')
    (Fin.cases ee (Fin.cases bb (Fin.cases aa (fun _ => kk))))
  simp only [φ,fv_space_sat_l hZF.1] at copied
  exact ⟨E,E',he,ee,(fv_space_l (ZF.modelsKP hZF) hb space).mp fe,
    (fv_space_l (ZF.modelsKP hZF) hb space').mp (copied.mp fe)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 反射壳中的可数模型与原函数图

目标秩层包含可数性单射图，故像中可数传递模型的全部成员均有原像。
Mostowski 唯一性固定该模型；随后逐个固定函数图的实际有序对。
这些结论不要求反射壳满足任何集合论模式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.fixed_preimage_l {ω c d X R Y S π A B : M.Domain}
    (hw : M.IsOmega ω) (xt : M.TransitiveSet X)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (map : Smap_d I ω c d X Y π)
    (image : Rd_entry_d A B π) (point : ∀ x, M.mem x B → Rd_entry_d x x π) : A = B := by
  apply hZF.1.eq_of_same_members
  intro x
  constructor
  · intro hx
    obtain ⟨y,_,xy⟩ := map.1.1.2.2 x (xt A (map.1.1.input_mem_of_pairMember image) x hx)
    have hy := (map.member_l I hZF hw mx my xy image).mp hx
    exact map.1.2 x y y xy (point y hy) ▸ hy
  · intro hx
    exact (map.member_l I hZF hw mx my (point x hx) image).mpr hx

theorem Smap_d.value_preimage_l {ω c d X R Y S π a b f g y : M.Domain}
    (hw : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (map : Smap_d I ω c d X Y π)
    (ab : Rd_entry_d a b π) (fg : Rd_entry_d f g π)
    (fn : M.IsSetFunction I g) (edge : Rd_entry_d b y g) :
    ∃ x, Rd_entry_d a x f ∧ Rd_entry_d x y π := by
  have hy := (edge.choose_spec.1.mem_l M yt
    (yt g (map.1.1.output_mem_of_pairMember fg) _ edge.choose_spec.2)).2
  have tr := map.exists_delta_l hZF hw xt yt mx my (n := 2)
    (rd_entry0_m (.bound 1) .newest (.bound 2)) (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
    ⟨Fin.cases a (fun _ => f),fun _ => f⟩ ⟨Fin.cases b (fun _ => g),fun _ => g⟩
    (Fin.cases ab (fun _ => fg))
  simp only [rd_entry0_sat_l hZF.1] at tr
  obtain ⟨x,hx,ax⟩ := tr.mpr ⟨y,hy,edge⟩
  obtain ⟨z,_,xz⟩ := map.1.1.2.2 x hx
  exact ⟨x,ax,fn.2 b z y ((map.entry_l hZF hw xt yt mx my ab xz fg).mp ax) edge ▸ xz⟩

variable {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
  {n} {v : Fin n → M.Domain}
  (h : Rf_hull_d hZF ω T Φ v α V d S P c R π) (hw : M.IsOmega ω)
include h hw

/-- 已固定坐标的有序对也在壳中，故整体固定。 -/
theorem Rf_hull_d.pair_fixed_l {p a b : M.Domain}
    (pair : KPair_d M p a b) (ha : Rd_entry_d a a π) (hb : Rd_entry_d b b π) : Rd_entry_d p p π := by
  let N := smdl_structure_l I (R := R) h.model.1.2.1
  have ext := smem_ext_l I h.model.1 h.model.2 h.transitive hZF.1
  let J := kpair_interpretation_l N ext (h.pairs_l hZF hw)
  obtain ⟨q,hq⟩ := J.total ⟨a,h.map.1.1.input_mem_of_pairMember ha⟩ ⟨b,h.map.1.1.input_mem_of_pairMember hb⟩
  have eq := kpair_unique_l M hZF.1
    (image_kpair_l (M := N) (N := M) Subtype.val (smem_full_l I h.model h.transitive) hq) pair
  exact h.map.fixed_pair_l hZF hw h.transitive (v_transitive_l I h.rank) h.model h.target (eq ▸ q.property) pair ha hb

/-- 像中的可数传递模型连同其原代码固定；可数性只要求在背景中成立。 -/
theorem Rf_hull_d.model_fixed_l (hω : M.mem ω P) {a b X U : M.Domain}
    (image : Rd_entry_d a b π) (model : Smem_d I b X U)
    (trans : M.TransitiveSet X) (count : M.CardinalLessOrEqual I X ω) :
    Rd_entry_d b b π ∧ Rd_entry_d X X π ∧ ∀ x, M.mem x X → Rd_entry_d x x π := by
  have vt := v_transitive_l I h.rank
  obtain ⟨A,B,_,_,_,ax,bu⟩ := h.map.kpair_preimage_l hZF hw h.transitive vt h.model h.target image model.1.1
  obtain ⟨ι,inj⟩ := count
  obtain ⟨D,prod⟩ := ZF.exists_cartesianProduct hZF I X ω
  have dV := ZF.v_product_mem_l I hZF h.rank h.limit (h.map.1.1.output_mem_of_pairMember ax)
    (h.map.1.1.output_mem_of_pairMember (h.map.omega_l I hZF hw h.transitive vt h.model h.target hω)) prod
  have iV := v_subset_mem_l I h.rank dV (fun p hp => by
    obtain ⟨x,y,pair⟩ := inj.1.1.1 p hp
    exact (prod p).mpr ⟨x,inj.1.input_mem_of_pairMember ⟨p,pair,hp⟩,
      y,inj.1.output_mem_of_pairMember ⟨p,pair,hp⟩,pair⟩)
  obtain ⟨_,_,_,cover⟩ := h.map.countable_preimage_l hZF hw h.transitive vt h.model h.target hω ax iV inj
  obtain ⟨_,point⟩ := mem_embedding_fixed_l hZF h.transitive h.map.1
    (fun _ _ _ _ hx hy => h.map.member_l I hZF hw h.model h.target hx hy) trans
    (fun x hx => (cover x hx).imp fun _ h => h.2)
  have eq := h.map.fixed_preimage_l hZF hw h.transitive h.model h.target ax point
  have fixed := eq ▸ ax
  have rel := h.map.relation_preimage_l hZF hw h.transitive vt h.model h.target fixed point bu model.1.2.2
  exact ⟨h.pair_fixed_l hZF hw model.1.1 fixed (rel ▸ bu),fixed,point⟩

/-- 函数的输入固定，输出按实际原像固定，则整张原函数图固定。 -/
theorem Rf_hull_d.function_fixed_l {f g : M.Domain} (image : Rd_entry_d f g π)
    (fn : M.IsSetFunction I g)
    (inputs : ∀ x y, Rd_entry_d x y g → Rd_entry_d x x π)
    (outputs : ∀ x y a, Rd_entry_d x y g → Rd_entry_d a y π → Rd_entry_d y y π) : f = g := by
  apply h.map.fixed_preimage_l hZF hw h.transitive h.model h.target image
  intro p hp
  obtain ⟨x,y,pair⟩ := fn.1 p hp
  have xy : Rd_entry_d x y g := ⟨p,pair,hp⟩
  obtain ⟨a,_,ay⟩ := h.map.value_preimage_l hZF hw h.transitive (v_transitive_l I h.rank)
    h.model h.target (inputs x y xy) image fn xy
  exact h.pair_fixed_l hZF hw pair (inputs x y xy) (outputs x y a xy ay)

end YesMetaZFC.SetTheory.Internal

/-! ## 弱测试壳回拉同一完整局面编号

有限自然数图逐点固定，局面空间由完整性唯一确定。编号的输入与每个
实际输出都固定，因此其整张图固定；规范性由原实际编号传回背景。
不把规范编码公式误作 Δ₀，也不要求测试壳满足 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rf_hull_d.game_number_l {ω Z α V d S P c R π : M.Domain} {Φ : List Lr_formula}
    {n} {v : Fin n → M.Domain} (h : Rf_hull_d hZF ω Z Φ v α V d S P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P) {T T' E E' : M.Domain}
    (finite : Fseq_space_d I ω ω T) (tt : Rd_entry_d T T' π) (ee : Rd_entry_d E E' π)
    (number : Gs_number_d I ω T' E') : Gs_number_d I ω T E := by
  have vt := v_transitive_l I h.rank
  have fixed := h.map.omega_l I hZF hw h.transitive vt h.model h.target hω
  have nat := h.map.natural_l hZF hw h.transitive vt h.model h.target hω
  have moved := h.fseq_image_l hZF hw hω fixed tt finite
  have eT : T = T' := hZF.1.eq_of_same_members _ _ (fun s => (finite s).trans (moved s).symm)
  have fixedT : Rd_entry_d T T π := eT.symm ▸ tt
  have points s (hs : M.mem s T) : Rd_entry_d s s π := by
    obtain ⟨m,hm,fn⟩ := (finite s).mp hs
    exact h.map.fixed_function_l hZF hw h.transitive vt h.model h.target
      (nat m hm) (fun i hi => nat i (hw.transitive (ZF.modelsKP hZF) m hm i hi)) hω
      (h.transitive T (h.map.1.1.input_mem_of_pairMember tt) s hs)
      (fn0_of_function_l (ZF.modelsKP hZF) fn) (fun _ a edge => nat a (fn.output_mem_of_pairMember edge))
  have fn := (h.map.function_l hZF hw h.transitive vt h.model h.target tt fixed ee).mpr
    (fn0_of_function_l (ZF.modelsKP hZF) number.function.1)
  have fixedE := h.map.fixed_function_l hZF hw h.transitive vt h.model h.target fixedT points hω
    (h.map.1.1.input_mem_of_pairMember ee) fn (fun _ a edge => nat a (fn.bound_l edge).2)
  have eE : E = E' := h.map.1.1.1.2 _ _ _ fixedE ee
  simpa only [eT,eE] using number

end YesMetaZFC.SetTheory.Internal

/-! ## 有界定义的完整关系图留在反射壳中

像图是像载体平方的子集，故属于原极限秩层。把图的有界成员方程
沿反坍塌取回，得到原参数定义的完整背景关系图，无需壳内收集模式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def rg_slots_l {n} : Fin (n+2) → Fin (n+4) :=
  Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ.succ))

def rg_graph_m {n} (φ : Delta0BinarySchema n) : Formula 1 (n+2) :=
  .conj (Formula.forallMem (.bound 0) (Formula.existsMem (.bound 2)
    (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest))))
    (Formula.forallMem (.bound 1) (Formula.forallMem (.bound 2)
      (.iff (rd_entry0_m (.bound 1) .newest (.bound 2)) (φ.body.rename rg_slots_l))))

@[simp] theorem rg_graph_closed_l {n} (φ : Delta0BinarySchema n) : (rg_graph_m φ).FreeClosed := by
  simp -implicitDefEqProofs [rg_graph_m,Definitional.Formula.FreeClosed,φ.freeClosed]

theorem rg_graph_delta_l {n} (φ : Delta0BinarySchema n) : (rg_graph_m φ).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..) (φ.delta0.rename_l _))))

theorem rg_graph_sat_l (hE : Extensional M) {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (A f : M.Domain) :
    Formula.satisfies ((ρ.push A).push f) (rg_graph_m φ) ↔
      (∀ p, M.mem p f → ∃ a, M.mem a A ∧ ∃ b, M.mem b A ∧ KPair_d M p a b) ∧
      ∀ a b, Rd_entry_d a b f ↔ M.mem a A ∧ M.mem b A ∧ φ.toBinarySchema.denote ρ a b := by
  have eval a b : Formula.satisfies ((((ρ.push A).push f).push a).push b) (φ.body.rename rg_slots_l) ↔
      φ.toBinarySchema.denote ρ a b := by
    rw [Formula.satisfies_rename]
    have env : ((((ρ.push A).push f).push a).push b).reindex rg_slots_l = (ρ.push a).push b := by
      rw [Env.mk.injEq]
      constructor
      · exact funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
      · rfl
    rw [env]
    rfl
  simp only [rg_graph_m,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff,kpair0_sat_l hE,Formula.satisfies_iff_iff,rd_entry0_sat_l hE,eval]
  constructor
  · rintro ⟨shape,rule⟩
    refine ⟨shape,fun a b => ⟨?_,?_⟩⟩
    · rintro ⟨p,pair,hp⟩
      obtain ⟨x,hx,y,hy,code⟩ := shape p hp
      obtain ⟨rfl,rfl⟩ := kpair_injective_l M code pair
      exact ⟨hx,hy,(rule x hx y hy).mp ⟨p,pair,hp⟩⟩
    · rintro ⟨ha,hb,hφ⟩
      exact (rule a ha b hb).mpr hφ
  · rintro ⟨shape,rule⟩
    exact ⟨shape,fun a ha b hb => (rule a b).trans ((and_iff_right ha).trans (and_iff_right hb))⟩

/-- 壳对自身参数定义的有界关系图封闭；构造由下面的反射定理给出。 -/
def Rg_closed_d (J : kpair_convention_l.Interpretation M) (P : M.Domain) : Prop :=
  ∀ {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (A : M.Domain),
    M.mem A P → (∀ i, M.mem (ρ.bound i) P) →
    ∃ f, M.mem f P ∧ M.IsSetRelation J f ∧
      ∀ a b, Rd_entry_d a b f ↔ M.mem a A ∧ M.mem b A ∧ φ.toBinarySchema.denote ρ a b

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rf_hull_d.graph_l {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
    {k} {v : Fin k → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
    (hw : M.IsOmega ω) : Rg_closed_d I P := by
  intro n φ ρ A hA params
  obtain ⟨B,hB,ab⟩ := h.map.1.1.2.2 A hA
  obtain ⟨w,images⟩ := Classical.axiomOfChoice (fun i =>
    (h.map.1.1.2.2 (ρ.bound i) (params i)).imp fun y hy => hy.2)
  let η : Env M n := ⟨w,fun _ => B⟩
  obtain ⟨g,rel,graph⟩ := ZF.exists_setRelationOn_of_denote hZF I φ.toBinarySchema η B
  obtain ⟨D,prod⟩ := ZF.exists_cartesianProduct hZF I B B
  have hd := ZF.v_product_mem_l I hZF h.rank h.limit hB hB prod
  have hg := v_subset_mem_l I h.rank hd (fun p hp => by
    obtain ⟨a,b,pair⟩ := rel.1 p hp
    have bound := rel.2 a b ⟨p,pair,hp⟩
    exact (prod p).mpr ⟨a,bound.1,b,bound.2,pair⟩)
  have tr := h.map.exists_delta_l hZF hw h.transitive (v_transitive_l I h.rank) h.model h.target
    (rg_graph_m φ) (rg_graph_closed_l φ) (rg_graph_delta_l φ) (ρ.push A) (η.push B) (Fin.cases ab images)
  simp only [rg_graph_sat_l hZF.1] at tr
  obtain ⟨f,hf,shape,entries⟩ := tr.mpr ⟨g,hg,⟨fun p hp => by
    obtain ⟨a,b,pair⟩ := rel.1 p hp
    have bound := rel.2 a b ⟨p,pair,hp⟩
    exact ⟨a,bound.1,b,bound.2,pair⟩,graph⟩⟩
  exact ⟨f,hf,fun p hp => (shape p hp).elim fun a ha => ha.2.elim fun b hb => ⟨a,b,hb.2⟩,entries⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 返回目标的实际序数界留在有限反射壳内

在像目标中分离全部序数。所得初段是目标的子集，因而属于原秩层；
它的有界成员方程沿反坍塌回收。下游只消费序数性和严格上界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Oh_bound_d (Y θ : M.Domain) : Prop where
  ordinal : M.IsOrdinal θ
  bound : ∀ α, M.mem α Y → M.IsOrdinal α → M.mem α θ

def oh_cut_m {n} (Y θ : Term n) : Formula 1 n :=
  .conj (KP.ord0_m θ) (.conj (Formula.subset θ Y)
    (Formula.forallMem Y (.iff (.mem .newest θ.weaken) (KP.ord0_m .newest))))
derive_free_closed oh_cut_m

theorem oh_cut_delta_l {n} (Y θ : Term n) : (oh_cut_m Y θ).IsDelta0 :=
  .conj (KP.ord0_delta_l _) (.conj (.atom ..) (.forallMem _ (.iff (.mem ..) (KP.ord0_delta_l _))))

theorem oh_cut_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (Y θ : Term n) :
    Formula.satisfies ρ (oh_cut_m Y θ) ↔ M.IsOrdinal (θ.eval ρ) ∧
      ∀ α, M.mem α (θ.eval ρ) ↔ M.mem α (Y.eval ρ) ∧ M.IsOrdinal α := by
  simp only [oh_cut_m,Formula.satisfies_conj_iff,KP.ord0_sat_l hKP,Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨ordinal,sub,rule⟩
    exact ⟨ordinal,fun α => ⟨fun h => ⟨sub α h,(rule α (sub α h)).mp h⟩,
      fun ⟨h,o⟩ => (rule α h).mpr o⟩⟩
  · rintro ⟨ordinal,rule⟩
    exact ⟨ordinal,fun α h => ((rule α).mp h).1,
      fun α h => (rule α).trans (and_iff_right h)⟩

/-- 传递集合的实际序数高度由有界分离给出，只需背景 KP。 -/
theorem oh_cut_exists_l (hKP : M.Models KP) {P : M.Domain} (pt : M.TransitiveSet P) :
    ∃ β, M.IsOrdinal β ∧ ∀ α, M.mem α β ↔ M.mem α P ∧ M.IsOrdinal α := by
  let φ : Delta0UnarySchema 0 := { body := KP.ord0_m .newest, delta0 := KP.ord0_delta_l _ }
  obtain ⟨β,sep⟩ := KP.separation_exists_d hKP φ ⟨Fin.elim0,fun _ => P⟩ P
  have cut α : M.mem α β ↔ M.mem α P ∧ M.IsOrdinal α :=
    (sep α).trans (and_congr_right fun _ => KP.ord0_sat_l hKP _ _)
  have bt : M.TransitiveSet β := fun α hα γ hγ =>
    (cut γ).mpr ⟨pt α ((cut α).mp hα).1 γ hγ,((cut α).mp hα).2.mem hγ⟩
  exact ⟨β,KP.ordinal_of_transitive_l hKP bt (fun α hα => ((cut α).mp hα).2),cut⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 高度的单射直接继承自原传递集合；无须把高度作为额外可数参数。 -/
theorem oh_countable_l {P ω : M.Domain} (pt : M.TransitiveSet P) (count : M.CardinalLessOrEqual I P ω) :
    ∃ β, Oh_bound_d P β ∧ M.CardinalLessOrEqual I β ω := by
  obtain ⟨β,ordinal,cut⟩ := oh_cut_exists_l (ZF.modelsKP hZF) pt
  obtain ⟨f,inc⟩ := ZF.exists_inclusionInjection hZF I (fun α hα => ((cut α).mp hα).1)
  obtain ⟨g,small⟩ := count
  exact ⟨β,⟨ordinal,fun α hα oα => (cut α).mpr ⟨hα,oα⟩⟩,ZF.exists_compositionInjection hZF I inc small⟩

theorem Rf_hull_d.height_l {ω T α V d S P c R π Y : M.Domain} {Φ : List Lr_formula}
    {n} {v : Fin n → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
    (hw : M.IsOmega ω) (hY : M.mem Y P) (yt : M.TransitiveSet Y) :
    ∃ θ, M.mem θ P ∧ Oh_bound_d Y θ := by
  obtain ⟨Z,hZ,yz⟩ := h.map.1.1.2.2 Y hY
  have tr := smap_delta_l I hZF hw h.transitive (v_transitive_l I h.rank) h.model h.target h.map (n := 1)
    (Formula.forallMem .newest (Formula.subset .newest (.bound 1)))
    (by simp -implicitDefEqProofs) (.forallMem _ (.atom ..))
    ⟨fun _ => Y,fun _ => Y⟩ ⟨fun _ => Z,fun _ => Z⟩ (fun _ => yz)
  simp only [Formula.satisfies_forallMem_iff,Formula.satisfies_subset_iff] at tr
  have zt := tr.mp yt
  obtain ⟨η,ordinal,cut⟩ := oh_cut_exists_l (ZF.modelsKP hZF) zt
  have hη := v_subset_mem_l I h.rank hZ (fun β hβ => ((cut β).mp hβ).1)
  have recover := h.map.exists_delta_l hZF hw h.transitive (v_transitive_l I h.rank) h.model h.target (n := 1)
    (oh_cut_m (.bound 1) .newest) (by simp -implicitDefEqProofs) (oh_cut_delta_l ..)
    ⟨fun _ => Y,fun _ => Y⟩ ⟨fun _ => Z,fun _ => Z⟩ (fun _ => yz)
  simp only [oh_cut_sat_l (ZF.modelsKP hZF)] at recover
  obtain ⟨θ,hθ,ord,cut⟩ := recover.mpr ⟨η,hη,ordinal,cut⟩
  exact ⟨θ,hθ,ord,fun β hβ oβ => (cut β).mpr ⟨hβ,oβ⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原实数参数及整个实数集的精确反坍塌像

自然数图逐点固定。测试壳实数集的像则是背景的完整 Baire 空间；
全部背景实数图由 ω×ω 的秩界覆盖，不把集合的像误写为逐点像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
  {n} {v : Fin n → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
  (hw : M.IsOmega ω) (hω : M.mem ω P)
include h hw hω

theorem Rf_hull_d.real_fixed_l {x : M.Domain} (hx : M.mem x P) (fx : Fn0_d ω ω x) : Rd_entry_d x x π := by
  have vt := v_transitive_l I h.rank
  have fixed := h.map.omega_l I hZF hw h.transitive vt h.model h.target hω
  have nat := h.map.natural_l hZF hw h.transitive vt h.model h.target hω
  obtain ⟨y,_,xy⟩ := h.map.1.1.2.2 x hx
  have fn := fn0_function_l (ZF.modelsKP hZF)
    ((h.map.function_l hZF hw h.transitive vt h.model h.target fixed fixed xy).mp fx)
  have eq := h.function_fixed_l hZF hw xy fn.1
    (fun a b ab => nat a (fn.input_mem_of_pairMember ab))
    (fun a b _ ab _ => nat b (fn.output_mem_of_pairMember ab))
  exact eq.symm ▸ xy

theorem Rf_hull_d.real_image_l {B : M.Domain} (hB : M.mem B P) (reals : Rb_reals_d P ω B) :
    ∃ C, Rd_entry_d B C π ∧ Baire_d I ω C := by
  have vt := v_transitive_l I h.rank
  have fixed := h.map.omega_l I hZF hw h.transitive vt h.model h.target hω
  have hωV := h.map.1.1.output_mem_of_pairMember fixed
  obtain ⟨D,prod⟩ := ZF.exists_cartesianProduct hZF I ω ω
  have hd := ZF.v_product_mem_l I hZF h.rank h.limit hωV hωV prod
  have owned x (fx : Fn0_d ω ω x) : M.mem x V := v_subset_mem_l I h.rank hd (fun p hp => by
    obtain ⟨a,ha,b,hb,pair⟩ := fx.1 p hp
    exact (prod p).mpr ⟨a,ha,b,hb,pair⟩)
  obtain ⟨C,hC,bc⟩ := h.map.1.1.2.2 B hB
  let φ : Formula 1 3 := .iff (.mem .newest (.bound 1)) (fn0_m (.bound 2) (.bound 2) .newest)
  have tr := h.map.forall_delta_l hZF hw h.transitive vt h.model h.target φ
    (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed]) (.iff (.mem ..) (fn0_delta_l ..))
    ⟨Fin.cases B (fun _ => ω),fun _ => ω⟩ ⟨Fin.cases C (fun _ => ω),fun _ => ω⟩ (Fin.cases bc (fun _ => fixed))
  simp only [φ,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,fn0_sat_l hZF.1] at tr
  have read := tr.mp (fun x hx => (reals x).trans (and_iff_right hx))
  refine ⟨C,bc,hw,fun x => ⟨?_,?_⟩⟩
  · intro hx
    exact fn0_function_l (ZF.modelsKP hZF) ((read x (vt C hC x hx)).mp hx)
  · intro fn
    have fx := fn0_of_function_l (ZF.modelsKP hZF) fn
    exact (read x (owned x fx)).mpr fx

end YesMetaZFC.SetTheory.Internal

/-! ## 测试壳的全部实数构成壳内实际集合

原极限秩层包含 ω×ω 的幂集，故包含实际函数空间。完整反坍塌映射
反映其存在句；有界函数图绝对性把原见证识别为壳的精确背景实数集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rf_hull_d.reals_l {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
    {n} {v : Fin n → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P) : ∃ B, M.mem B P ∧ Rb_reals_d P ω B := by
  have vt := v_transitive_l I h.rank
  have fixed := h.map.omega_l I hZF hw h.transitive vt h.model h.target hω
  have hωV := h.map.1.1.output_mem_of_pairMember fixed
  obtain ⟨D,prod⟩ := ZF.exists_cartesianProduct hZF I ω ω
  have hd := ZF.v_product_mem_l I hZF h.rank h.limit hωV hωV prod
  obtain ⟨U,power⟩ := v_power_exists_l I (ZF.modelsKP hZF) h.rank hd
  have hu := v_power_mem_l I h.rank h.limit hd power
  obtain ⟨B,space⟩ := ZF.exists_functionSpace hZF I ω ω
  have hb := v_subset_mem_l I h.rank hu (fun f hf => (power f).mpr (fun p hp => by
    have fn := (space f).mp hf
    obtain ⟨a,b,pair⟩ := fn.1.1 p hp
    exact (prod p).mpr ⟨a,fn.input_mem_of_pairMember ⟨p,pair,hp⟩,
      b,fn.output_mem_of_pairMember ⟨p,pair,hp⟩,pair⟩))
  let N := smdl_structure_l I (R := R) h.model.1.2.1
  let L := smdl_structure_l I (R := S) h.target.1.2.1
  let Ω : N.Domain := ⟨ω,hω⟩
  let W : L.Domain := ⟨ω,hωV⟩
  let ρ : Env N 1 := ⟨fun _ => Ω,fun _ => Ω⟩
  let η : Env L 1 := ⟨fun _ => W,fun _ => W⟩
  let φ : Formula 1 1 := .existsE (.forallE
    (.iff (.mem .newest (.bound 1)) (fn0_m (.bound 2) (.bound 2) .newest)))
  have target : Formula.satisfies η φ := by
    simp only [φ,Formula.satisfies_exists_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff,fn0_sat_l (smem_ext_l I h.target.1 h.target.2 vt hZF.1)]
    refine ⟨(⟨B,hb⟩ : L.Domain),fun f => ?_⟩
    exact (smem_member_l I h.target.1 h.target.2 f ⟨B,hb⟩).trans
      ((space f.val).trans ((show M.IsSetFunctionFromTo I f.val ω ω ↔ Fn0_d ω ω f.val from
        ⟨fn0_of_function_l (ZF.modelsKP hZF),fn0_function_l (ZF.modelsKP hZF)⟩).trans
          (smem_fn0_l I hZF.1 h.target vt W W f).symm))
  have source := (smap_source_l I hZF hw h.model.1 h.target.1 h.map φ
    (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed]) ρ η (fun _ => fixed)).mpr target
  have existsB : ∃ B : N.Domain, ∀ x, N.mem x B ↔ Fn0_d Ω Ω x := by
    simpa only [φ,Formula.satisfies_exists_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff,fn0_sat_l (smem_ext_l I h.model.1 h.model.2 h.transitive hZF.1)] using! source
  obtain ⟨B,read⟩ := existsB
  refine ⟨B.val,B.property,fun x => ⟨?_,?_⟩⟩
  · intro hx
    let x₀ : N.Domain := ⟨x,h.transitive B.val B.property x hx⟩
    exact ⟨x₀.property,(smem_fn0_l I hZF.1 h.model h.transitive Ω Ω x₀).mp
      ((read x₀).mp ((smem_member_l I h.model.1 h.model.2 x₀ B).mpr hx))⟩
  · rintro ⟨hx,fx⟩
    let x₀ : N.Domain := ⟨x,hx⟩
    exact (smem_member_l I h.model.1 h.model.2 x₀ B).mp
      ((read x₀).mpr ((smem_fn0_l I hZF.1 h.model h.transitive Ω Ω x₀).mpr fx))

end YesMetaZFC.SetTheory.Internal

/-! ## 同一坏收益在弱测试壳中的实际回拉

原有界证书沿反坍塌同时回拉。自然数及指定二值实数逐点固定；实数集
识别为壳的精确实数迹，种子为该迹的真实最小传递闭包，局面空间则
仍包含全部背景内部有限图。Jensen 证书在背景解码，不假设测试壳满足 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel InnerModel.Relative Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rf_hull_d.counterexample_l {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
    {n} {v : Fin n → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P) {φ : Formula 1 4} (hc : φ.FreeClosed)
    {x y : Fin 18 → M.Domain} (ew : x 0 = ω) (images : ∀ i, Rd_entry_d (y i) (x i) π)
    (space : Baire_d I ω (x 2)) (bad : Jp_counter_d φ x) :
    y 0 = ω ∧ y 4 = x 4 ∧ Rb_reals_d P ω (y 2) ∧ Tc_d (y 2) (y 1) ∧
      Fseq_space_d I ω ω (y 3) ∧ Jp_counter_d φ y ∧ Jp_d I φ (y 1) (y 2) (y 4) (y 5) (y 6) ∧
      ¬ Gs_det_d ω (y 2) (y 3) (y 7) (y 8) (y 6) := by
  have vt := v_transitive_l I h.rank
  have fixed := h.map.omega_l I hZF hw h.transitive vt h.model h.target hω
  have zeroImage : Rd_entry_d (y 0) ω π := by rw [← ew]; exact images 0
  have sw : y 0 = ω := h.map.1.2 _ _ _ zeroImage fixed
  let ρ : Env M 18 := ⟨y,fun _ => ω⟩
  let η : Env M 18 := ⟨x,fun _ => ω⟩
  have transfer := smap_delta_l I hZF hw h.transitive vt h.model h.target h.map
    (jp_counter_m φ) (jp_counter_closed_l hc) (jp_counter_delta_l φ) ρ η images
  have data := (jp_counter_sat_l (ZF.modelsKP hZF) hc ρ).mp
    (transfer.mpr ((jp_counter_sat_l (ZF.modelsKP hZF) hc η).mpr bad))
  have binary : Bc_binary_d ω (y 4) := sw ▸ data.binary
  have ha := h.map.1.1.input_mem_of_pairMember (images 4)
  have sa : y 4 = x 4 := h.map.1.1.1.2 _ _ _ (h.real_fixed_l hZF hw hω ha binary.1) (images 4)
  -- 完整像实数集的唯一性识别原像；不把壳内实数误认为背景全部实数。
  obtain ⟨B,hB,reals⟩ := h.reals_l hZF hw hω
  obtain ⟨C,bc,complete⟩ := h.real_image_l hZF hw hω hB reals
  have eC : C = x 2 := hZF.1.eq_of_same_members _ _ (fun r => (complete.2 r).trans (space.2 r).symm)
  have eB : B = y 2 := h.map.1.2 _ _ _ (eC ▸ bc) (images 2)
  have trace : Rb_reals_d P ω (y 2) := eB ▸ reals
  have seed : Tc_d (y 2) (y 1) :=
    (rf_seed0_iff_l (ZF.modelsKP hZF) (hw.transitive (ZF.modelsKP hZF))
      (fun r hr => ((trace r).mp hr).2) ⟨y 4,(trace (y 4)).mpr ⟨ha,binary.1⟩⟩).mp (sw ▸ data.seed)
  -- 局面空间的像、原像均由完整有限图的成员方程唯一确定。
  obtain ⟨K,hK,finite⟩ := h.fseq_l hZF hw hω hω
  obtain ⟨K',_,kk⟩ := h.map.1.1.2.2 K hK
  have finite' := h.fseq_image_l hZF hw hω fixed kk finite
  have original : Fseq_space_d I ω ω (x 3) :=
    ((gs_base_iff_l hZF space).mp (ew ▸ bad.base)).1
  have eK' : K' = x 3 := hZF.1.eq_of_same_members _ _ (fun t => (finite' t).trans (original t).symm)
  have eK : K = y 3 := h.map.1.2 _ _ _ (eK' ▸ kk) (images 3)
  have present := (jp_local_iff_l hZF data.check.1 data.check.2.1 data.check.2.2.1 data.check.2.2.2.1).mpr
    data.check.2.2.2.2.1
  exact ⟨sw,sa,trace,seed,eK ▸ finite,data,present,sw ▸ data.check.2.2.2.2.2.2.2.1⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 实数集及其原最小传递种子同时留在测试壳

恒等自然数图给出壳内真实实数。非空函数族的传递闭包只需有限次
配对及并集，故原种子由反射壳已有的实际代数闭包构造。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 已实现的完整源模型包含整个非空函数族时，也包含同一背景最小传递种子。 -/
theorem smem_real_seed_l {c X R D B : M.Domain} (model : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) model.1.2.1).Models ZF)
    (hD : M.mem D X) (hB : M.mem B X) (dt : M.TransitiveSet D)
    (reals : ∀ x, M.mem x B → Fn0_d D D x) (ne : ∃ x, M.mem x B) :
    ∃ Z, M.mem Z X ∧ Tc_d B Z := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  let d : N.Domain := ⟨D,hD⟩
  let b : N.Domain := ⟨B,hB⟩
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I model trans
  have td : N.TransitiveSet d := by
    intro x hx y hy
    exact (smem_member_l I model.1 model.2 y d).mpr (dt x.val
      ((smem_member_l I model.1 model.2 x d).mp hx) y.val ((smem_member_l I model.1 model.2 y x).mp hy))
  obtain ⟨x,hx⟩ := ne
  let x₀ : N.Domain := ⟨x,trans B hB x hx⟩
  obtain ⟨Z,tc⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP native)) native b
  exact ⟨Z.val,Z.property,Relative.real_tc_image_l (ZF.modelsKP native) hZF.1 Subtype.val inj full td
    (fun x hx => (smem_fn0_l I hZF.1 model trans d d x).mpr
      (reals x.val ((smem_member_l I model.1 model.2 x b).mp hx)))
    ⟨x₀,(smem_member_l I model.1 model.2 x₀ b).mpr hx⟩ tc⟩

theorem Rf_hull_d.real_seed_l {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
    {n} {v : Fin n → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P) :
    ∃ B Z, M.mem B P ∧ M.mem Z P ∧ Rb_reals_d P ω B ∧ Tc_d B Z := by
  obtain ⟨B,hB,reals⟩ := h.reals_l hZF hw hω
  let φ : Delta0BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest, delta0 := .atom .. }
  let ρ : Env M 0 := ⟨Fin.elim0,fun _ => ω⟩
  obtain ⟨f,hf,relation,entries⟩ := h.graph_l hZF hw φ ρ ω hω (fun i => Fin.elim0 i)
  have graph a b : Rd_entry_d a b f ↔ M.mem a ω ∧ M.mem b ω ∧ a = b :=
    (entries a b).trans (and_congr_right fun _ => and_congr_right fun _ =>
      Formula.satisfies_extensionalEq_iff_eq hZF.1 ((ρ.push a).push b) (.bound 1) .newest)
  have fn : Fn0_d ω ω f := by
    refine ⟨?_,fun a ha => ⟨a,ha,(graph a a).mpr ⟨ha,ha,rfl⟩⟩,?_⟩
    · intro p hp
      obtain ⟨a,b,pair⟩ := relation p hp
      have bound := (graph a b).mp ⟨p,pair,hp⟩
      exact ⟨a,bound.1,b,bound.2.1,pair⟩
    · intro a _ b _ c _ ab ac
      exact ((graph a b).mp ab).2.2.symm.trans ((graph a c).mp ac).2.2
  have ne : ∃ x, M.mem x B := ⟨f,(reals f).mpr ⟨hf,fn⟩⟩
  have join {a b : M.Domain} (ha : M.mem a P) (hb : M.mem b P) :
      ∃ u, M.mem u P ∧ ∀ x, M.mem x u ↔ M.mem x a ∨ M.mem x b := by
    obtain ⟨p,hp,pair⟩ := h.pair_mem_l hZF hw ha hb
    obtain ⟨u,hu,un⟩ := h.union_mem_l hZF hw hp
    refine ⟨u,hu,fun x => (un x).trans ⟨?_,?_⟩⟩
    · rintro ⟨y,hy,xy⟩
      exact ((pair y).mp hy).elim (fun eq => Or.inl (eq ▸ xy)) (fun eq => Or.inr (eq ▸ xy))
    · intro hx
      exact hx.elim (fun ha => ⟨a,(pair a).mpr (Or.inl rfl),ha⟩)
        (fun hb => ⟨b,(pair b).mpr (Or.inr rfl),hb⟩)
  obtain ⟨U,hU,un⟩ := h.union_mem_l hZF hw hB
  obtain ⟨W,hW,un'⟩ := h.union_mem_l hZF hw hU
  obtain ⟨A,hA,a⟩ := join hW hω
  obtain ⟨D,hD,b⟩ := join hU hA
  obtain ⟨E,hE,e⟩ := join hB hD
  obtain ⟨Q,hQ,q⟩ := h.pair_mem_l hZF hw hB hB
  obtain ⟨Z,hZ,z⟩ := join hE hQ
  refine ⟨B,Z,hB,hZ,reals,Relative.rf_seed_l (hw.transitive (ZF.modelsKP hZF))
    (fun x hx => ((reals x).mp hx).2) ne un un' ?_⟩
  intro x
  rw [z x,e x,b x,a x,q x]
  simp only [or_self]
  exact or_comm

end YesMetaZFC.SetTheory.Internal
