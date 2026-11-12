import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.Model.SetTheory.Reflection.SkolemWitnessTree
import YesMetaZFC.SetTheory.BinaryWitnessClub
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.Forcing.Embedding.Rank
import YesMetaZFC.Model.SetTheory.Internal.Collapse
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed

/-! # 对原司寇伦图及给定泛型的见证同时闭合的可数壳

一个二参数公式同时要求留在原泛型、加强当前条件，并在枚举项为泛型条件时
加强它、在枚举项为稠密集时命中它。先细化为原司寇伦图的闭集 club，再按该
实际公式细化，得到同一个可数初等壳。原选择图和原泛型均保持指定对象。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}}

def Gh_step_d (Q T H p a q : M.Domain) : Prop := M.mem q H ∧ Entry_d M q p T ∧
  (M.mem a H → Entry_d M q a T) ∧ (Dense_set_d M Q T Q a → M.mem q a)

def gh_step_m {n} (Q T H p a q : Term n) : Formula 1 n := .conj (.mem q H)
  (.conj (entry_m q p T) (.conj (.imp (.mem a H) (entry_m q a T)) (.imp (dense_set_m Q T Q a) (.mem q a))))
derive_free_closed gh_step_m

theorem gh_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Q T H p a q : Term n) :
    Formula.satisfies ρ (gh_step_m Q T H p a q) ↔
      Gh_step_d (Q.eval ρ) (T.eval ρ) (H.eval ρ) (p.eval ρ) (a.eval ρ) (q.eval ρ) := by
  simp only [gh_step_m,Gh_step_d,Formula.satisfies_conj_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff,entry_sat_l M hE,dense_set_sat_l M hE]

def Gh_closed_d (Q T H N : M.Domain) : Prop := ∀ p a, M.mem p N → M.mem a N → M.mem p H →
  ∃ q, M.mem q N ∧ Gh_step_d Q T H p a q

/-- 真泛型中的共同加强和原稠密命中，实际提供这一个公式的见证。 -/
theorem gh_step_exists_l (hM : M.Models KP) {c X R H : M.Domain}
    (source : Smem_d (kp_pair_l hM) c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l (kp_pair_l hM) (R := R) source.1.2.1).Models ZF)
    (Q T : (smdl_structure_l (kp_pair_l hM) (R := R) source.1.2.1).Domain)
    (O : Cond_order_d (smdl_structure_l (kp_pair_l hM) (R := R) source.1.2.1) Q T Q)
    (generic : Generic_d (smdl_structure_l (kp_pair_l hM) (R := R) source.1.2.1) Q T Q (fun q => M.mem q.val H))
    (p a : (smdl_structure_l (kp_pair_l hM) (R := R) source.1.2.1).Domain) (hp : M.mem p.val H) :
    ∃ q, M.mem q X ∧ Gh_step_d Q.val T.val H p.val a.val q := by
  let N := smdl_structure_l (kp_pair_l hM) (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l (kp_pair_l hM) source trans
  have edge := image_entry_iff_l Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hM.1
  have start : ∃ r : N.Domain, M.mem r.val H ∧ Entry_d N r p T ∧ (M.mem a.val H → Entry_d N r a T) := by
    rcases Classical.em (M.mem a.val H) with ha | no
    · obtain ⟨r,hr,rp,ra⟩ := generic.directed p a hp ha
      exact ⟨r,hr,rp,fun _ => ra⟩
    · exact ⟨p,hp,O.refl p (generic.proper p hp).1,fun ha => (no ha).elim⟩
  obtain ⟨r,hr,rp,ra⟩ := start
  rcases Classical.em (Dense_set_d M Q.val T.val Q.val a.val) with dense | no
  · have dense' := (source.dense_code_l (kp_pair_l hM) hM.1 trans (ZF.modelsKP native) Q T Q a).mp dense
    obtain ⟨q,hq,qa,qr⟩ := generic.meets_below_l native O hr (fun s hs => dense'.2 s hs.1 hs.2.1)
    refine ⟨q.val,q.property,hq,(edge q p T).mp
      (O.trans q r p (generic.proper q hq).1 (generic.proper r hr).1 (generic.proper p hp).1 qr rp),?_,?_⟩
    · intro ha
      exact (edge q a T).mp (O.trans q r a (generic.proper q hq).1 (generic.proper r hr).1 (generic.proper a ha).1 qr (ra ha))
    · exact fun _ => (image_member_l Subtype.val inj full).mpr qa
  · exact ⟨r.val,r.property,hr,(edge r p T).mp rp,fun ha => (edge r a T).mp (ra ha),fun h => (no h).elim⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 给定的原司寇伦图和原泛型共同决定实际可数初等壳，包含任意给定可数种子。 -/
theorem gh_hull_l {ω c X R u C S T D K H B : M.Domain}
    (hw : M.IsOmega ω) (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (skolem : Ssk_d I ω c X u C S T D K)
    (Q V : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) Q V Q)
    (generic : Generic_d (smdl_structure_l I (R := R) source.1.2.1) Q V Q (fun q => M.mem q.val H))
    (sub : M.MemberSubset B X) (count : M.CardinalLessOrEqual I B ω) :
    ∃ N d R', M.MemberSubset B N ∧ M.MemberSubset N X ∧ M.CardinalLessOrEqual I N ω ∧
      Fc_closed_d I ω T K N ∧ Ssub_d I c d X R N R' ∧ Selem_d I ω c d ∧ Gh_closed_d Q.val V.val H N := by
  obtain ⟨id,identity⟩ := ZF.exists_identityBijection hZF I ω
  have countT := ZF.countable_product_l I hZF hw (scode_countable_l I hZF hw skolem.codes) ⟨id,identity.1⟩ skolem.labels
  obtain ⟨C₀,all,_⟩ := ZFC.cc_all_l I hZFC hw X
  obtain ⟨C₁,closed,read⟩ := ZFC.fc_club_refine_l I hZFC hw skolem.params skolem.domain skolem.graph countT all
  let ρ : Env M 3 := ⟨fun i => [Q.val,V.val,H].get i,fun _ => H⟩
  let φ : UnarySchema 5 := { body := gh_step_m (.bound 3) (.bound 4) (.bound 5) (.bound 2) (.bound 1) .newest }
  have sat p a q : φ.denote ((ρ.push p).push a) q ↔ Gh_step_d Q.val V.val H p a q := gh_step_sat_l hZF.1 ..
  obtain ⟨C₂,club,witness⟩ := ZFC.bw_club_l I hZFC hw closed φ ρ
  obtain ⟨N,hN,inside⟩ := club.unbounded B sub count
  have bounds := club.members N hN
  have closedN := ((read N).mp (witness N hN).1).2
  obtain ⟨d,R',submodel,elem⟩ := selem_of_skolem_l I hZF hw source.1 skolem.codes bounds.1
    (skolem.point_mem_l I hZF hw source.1 closedN) (skolem.closed_l I bounds.1 closedN)
  refine ⟨N,d,R',inside,bounds.1,bounds.2,closedN,submodel,elem,fun p a hp ha hH => ?_⟩
  obtain ⟨q,hq,step⟩ := gh_step_exists_l (ZF.modelsKP hZF) source trans native Q V O generic
    ⟨p,bounds.1 p hp⟩ ⟨a,bounds.1 a ha⟩ hH
  obtain ⟨q,hq,step⟩ := (witness N hN).2 p a hp ha ⟨q,hq,(sat p a q).mpr step⟩
  exact ⟨q,hq,(sat p a q).mp step⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 实际初等壳中的全局稠密判据

原内部初等证书给出实际壳模型的 ZF。其全局稠密集沿同一包含映射送到源，
壳内滤子的实际命中证据再由原公式全局化提升为完整泛型。此判据同时用于
给定原泛型的限制，以及联合枝实际生成的滤子，不预设后者已是源泛型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Gh_model_d (ω c X R N d S Q T H : M.Domain) : Prop where
  submodel : Ssub_d I c d X R N S
  elementary : Selem_d I ω c d
  conditions_mem : M.mem Q N
  order_mem : M.mem T N
  native : (smdl_structure_l I (R := S) submodel.target.2.1).Models ZF
  generic : Generic_d (smdl_structure_l I (R := S) submodel.target.2.1)
    ⟨Q,conditions_mem⟩ ⟨T,order_mem⟩ ⟨Q,conditions_mem⟩ (fun q => M.mem q.val H)

theorem gh_model_l {ω c X R N d S H : M.Domain} (hw : M.IsOmega ω)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (model : Ssub_d I c d X R N S) (elem : Selem_d I ω c d)
    (Q T : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) Q T Q)
    (hQ : M.mem Q.val N) (hT : M.mem T.val N)
    (proper : ∀ p, M.mem p N → M.mem p H → M.mem p Q.val)
    (upward : ∀ p q, M.mem p N → M.mem q N → M.mem p H → M.mem q Q.val → Entry_d M p q T.val → M.mem q H)
    (inhabited : ∃ p, M.mem p N ∧ M.mem p H)
    (directed : ∀ p q, M.mem p N → M.mem q N → M.mem p H → M.mem q H →
      ∃ r, M.mem r N ∧ M.mem r H ∧ Entry_d M r p T.val ∧ Entry_d M r q T.val)
    (hits : ∀ D, M.mem D N → Dense_set_d M Q.val T.val Q.val D → ∃ q, M.mem q N ∧ M.mem q H ∧ M.mem q D) :
    Gh_model_d hZF ω c X R N d S Q.val T.val H := by
  let A := smdl_structure_l I (R := S) model.target.2.1
  let B := smdl_structure_l I (R := R) source.1.2.1
  let j : A.Domain → B.Domain := fun x => ⟨x.val,model.subset x.val x.property⟩
  have element : Pe_d j := fun φ hc ρ => (selem_source_l I hZF hw model elem φ hc
    (image_env_l j ρ) ρ (fun _ => rfl)).symm
  have small := smem_sub_l I source model
  have ext := (selem_sigma1_sub_l I hZF hw source model elem).extensional_l hZF.1 trans
  have hA : Extensional A := ⟨fun x y same => Subtype.ext (ext x.val x.property y.val y.property (fun z hz =>
    (smem_member_l I small.1 small.2 ⟨z,hz⟩ x).symm.trans
      ((same ⟨z,hz⟩).trans (smem_member_l I small.1 small.2 ⟨z,hz⟩ y))))⟩
  have hAZF : A.Models ZF := by
    refine ⟨hA,fun φ hφ => ?_⟩
    rw [Structure.satisfiesSentence_iff]
    intro f
    have env : image_env_l j (⟨Fin.elim0,f⟩ : Env A 0) = ⟨Fin.elim0,fun i => j (f i)⟩ := by
      rw [Env.mk.injEq]
      exact ⟨funext (fun i => Fin.elim0 i),rfl⟩
    exact (element φ.formula φ.freeClosed ⟨Fin.elim0,f⟩).mpr (env.symm ▸
      (Structure.satisfiesSentence_iff B φ).mp (native.2 φ hφ) (fun i => j (f i)))
  have inj : Function.Injective (Subtype.val : B.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have edge a b t : Entry_d A a b t ↔ Entry_d M a.val b.val t.val :=
    (em_entry_l hA native.1 j element a b t).trans
      (image_entry_iff_l Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hZF.1 (j a) (j b) (j t))
  have member (a b : A.Domain) : A.mem a b ↔ M.mem a.val b.val := smem_member_l I small.1 small.2 a b
  let P : A.Domain := ⟨Q.val,hQ⟩
  let V : A.Domain := ⟨T.val,hT⟩
  have good p (hp : M.mem p.val H) : A.mem p P ∧ p ≠ P :=
    ⟨(member p P).mpr (proper p.val p.property hp),fun eq =>
      KP.mem_irrefl_d (ZF.modelsKP hAZF) P (eq ▸ (member p P).mpr (proper p.val p.property hp))⟩
  have order : Cond_order_d A P V P := by
    refine ⟨fun p hp => (em_entry_l hA native.1 j element p p V).mpr
      (O.refl (j p) ((em_member_l j element p P).mp hp)),?_,?_⟩
    · intro p q r hp hq hr pq qr
      exact (em_entry_l hA native.1 j element p r V).mpr (O.trans (j p) (j q) (j r)
        ((em_member_l j element p P).mp hp) ((em_member_l j element q P).mp hq) ((em_member_l j element r P).mp hr)
        ((em_entry_l hA native.1 j element p q V).mp pq) ((em_entry_l hA native.1 j element q r V).mp qr))
    · intro p hp pp
      exact Subtype.ext (congrArg (fun x : B.Domain => x.val) (O.zero (j p) ((em_member_l j element p P).mp hp)
        ((em_entry_l hA native.1 j element p P V).mp pp)))
  have dense (D : A.Domain) (hd : Dense_set_d A P V P D) : Dense_set_d M Q.val T.val Q.val D.val := by
    let ρ : Env A 3 := ⟨fun i => [P,V,D].get i,fun _ => P⟩
    have moved := (dense_set_sat_l B native.1 (image_env_l j ρ) (.bound 0) (.bound 1) (.bound 0) (.bound 2)).mp
      ((element (dense_set_m (.bound 0) (.bound 1) (.bound 0) (.bound 2)) (by simp -implicitDefEqProofs) ρ).mp
        ((dense_set_sat_l A hA ρ (.bound 0) (.bound 1) (.bound 0) (.bound 2)).mpr hd))
    exact (source.dense_code_l I hZF.1 trans (ZF.modelsKP native) Q T Q (j D)).mpr moved
  refine ⟨model,elem,hQ,hT,hAZF,good,?_,?_,?_,?_⟩
  · obtain ⟨p,hp,hH⟩ := inhabited
    exact ⟨⟨p,hp⟩,hH⟩
  · intro p q hp hq pq
    exact upward p.val q.val p.property q.property hp ((member q P).mp hq) ((edge p q V).mp pq)
  · intro p q hp hq
    obtain ⟨r,hr,hH,rp,rq⟩ := directed p.val q.val p.property q.property hp hq
    exact ⟨⟨r,hr⟩,hH,(edge ⟨r,hr⟩ p V).mpr rp,(edge ⟨r,hr⟩ q V).mpr rq⟩
  · intro p hp D hd
    obtain ⟨E,global,read⟩ := dense_globalize_l hAZF order (good p hp).1 hd
    obtain ⟨r,hr,hH,rE⟩ := hits E.val E.property (dense E global)
    let q : A.Domain := ⟨r,hr⟩
    have qE := (member q E).mpr rE
    rcases ((read q).mp qE).2.2 with no | hit
    · obtain ⟨s,hs,hS,sq,sp⟩ := directed r p.val hr p.property hH hp
      let t : A.Domain := ⟨s,hs⟩
      exact (no ⟨t,⟨(good t hS).1,(good t hS).2,(edge t q V).mpr sq⟩,(edge t p V).mpr sp⟩).elim
    · exact ⟨q,hH,hit.2⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同一初等壳及其泛型的传递坍塌

Mostowski 图给出两向完整初等性，原源的内部 ZFC 沿返回嵌入回拉。
泛型集合由原滤子在坍塌图下的实际像分离而成，保留每个壳内条件的归属。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 可数泛型壳的实际坍塌资料；两个滤子由同一坍塌图逐条件对应。 -/
structure Gh_collapse_d (ω c X N d Q T H B F j e V P U G : M.Domain) : Prop where
  transitive : M.TransitiveSet B
  collapse : Mc_iso_d N B F
  inverse : M.IsSetBijectionFromTo I j B N
  inverse_entries : ∀ x y, Rd_entry_d y x j ↔ Rd_entry_d x y F
  model : Smem_d I e B V
  forward : Smap_d I ω d e N B F
  embedding : Smap_d I ω e c B X j
  theory : Zc_model_d I ω e B V
  countable : M.CardinalLessOrEqual I B ω
  conditions : Rd_entry_d Q P F
  order : Rd_entry_d T U F
  generic : Gset_d P U P B G
  members : ∀ x, M.mem x G ↔ M.mem x B ∧ ∃ p, Rd_entry_d p x F ∧ M.mem p H

theorem Gh_model_d.collapse_l {ω c X R N d S Q T H : M.Domain} (hw : M.IsOmega ω)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X) (certificate : Zc_model_d I ω c X R)
    (h : Gh_model_d hZF ω c X R N d S Q T H) (count : M.CardinalLessOrEqual I N ω) :
    ∃ B F j e V P U G, Gh_collapse_d hZF ω c X N d Q T H B F j e V P U G := by
  have small := smem_sub_l I source h.submodel
  obtain ⟨B,F,bt,collapse,_⟩ := mc_collapse_l (ZF.models_kpi_l hZF)
    ((selem_sigma1_sub_l I hZF hw source h.submodel h.elementary).extensional_l hZF.1 trans)
  obtain ⟨e,V,j,model,forward,inverse,entries,back⟩ := mc_smaps_l hZF hw collapse small
  have embedding := back.target_sub_l I hZF.1 h.submodel h.elementary
  have theory := certificate.pull_l hZF hw model.1 embedding
  let A := smdl_structure_l I (R := S) h.submodel.target.2.1
  let C := smdl_structure_l I (R := V) model.1.2.1
  have native := ZFC.models_zf_l (theory.native_l I hZF hw)
  obtain ⟨f,elem,values⟩ := forward.project_l I hZF hw h.submodel.target model.1
  have onto : Function.Surjective f := by
    intro y
    obtain ⟨x,xy⟩ := collapse.onto y.val y.property
    let x₀ : A.Domain := ⟨x,(collapse.function.bound_l xy).1⟩
    exact ⟨x₀,Subtype.ext (forward.1.1.1.2 _ _ _ (values x₀) xy)⟩
  let p : A.Domain := ⟨Q,h.conditions_mem⟩
  let t : A.Domain := ⟨T,h.order_mem⟩
  let ρ : Env M 2 := ⟨fun i => [F,H].get i,fun _ => F⟩
  let φ : UnarySchema 2 := {
    body := .existsE (.conj (rd_entry0_m .newest (.bound 1) (.bound 2)) (.mem .newest (.bound 3))) }
  have read x : φ.denote ρ x ↔ ∃ a, Rd_entry_d a x F ∧ M.mem a H := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,Formula.satisfies_mem_iff]
    rfl
  obtain ⟨G,sep⟩ := ZF.separation_exists_d hZF φ ρ B
  have members x := (sep x).trans (and_congr_right fun _ => read x)
  have same : (fun x : C.Domain => M.mem x.val G) = Em_generic_d f (fun a => M.mem a.val H) := by
    funext x
    apply propext
    constructor
    · intro hx
      obtain ⟨_,a,ax,ha⟩ := (members x.val).mp hx
      let a₀ : A.Domain := ⟨a,(collapse.function.bound_l ax).1⟩
      exact ⟨a₀,ha,Subtype.ext (forward.1.1.1.2 _ _ _ (values a₀) ax)⟩
    · rintro ⟨a,ha,rfl⟩
      exact (members (f a).val).mpr ⟨(f a).property,a.val,values a,ha⟩
  have generic := em_generic_l h.native.1 (ZF.modelsKP native) f elem h.generic
    (fun x hx => by
      obtain ⟨a,rfl⟩ := onto x
      exact ⟨a,(em_member_l f elem a p).mpr hx,rfl⟩) (fun D _ => onto D)
  rw [← same] at generic
  have sub : M.MemberSubset G (f p).val := by
    intro x hx
    exact (smem_member_l I model.1 model.2 ⟨x,((members x).mp hx).1⟩ (f p)).mp
      (generic.proper ⟨x,((members x).mp hx).1⟩ hx).1
  obtain ⟨ι,fi⟩ := count
  exact ⟨B,F,j,e,V,(f p).val,(f t).val,G,bt,collapse,inverse,entries,model,forward,embedding,theory,
    ZF.exists_compositionInjection hZF I inverse.1 fi,values p,values t,
    (model.generic_code_l I hZF.1 bt (ZF.modelsKP native) (f p) (f t) (f p) G).mpr ⟨sub,generic⟩,members⟩

/-- 原壳里的每个条件与其坍塌值属于同一个泛型，不另换泛型。 -/
theorem Gh_collapse_d.accepted_l {ω c X N d Q T H B F j e V P U G p x : M.Domain}
    (h : Gh_collapse_d hZF ω c X N d Q T H B F j e V P U G) (px : Rd_entry_d p x F) :
    M.mem p H ↔ M.mem x G := by
  constructor
  · exact fun hp => (h.members x).mpr ⟨(h.collapse.function.bound_l px).2,p,px,hp⟩
  · intro hx
    obtain ⟨_,q,qx,hq⟩ := (h.members x).mp hx
    exact h.collapse.injective q p x qx px ▸ hq

/-- 传递坍塌自动含有真实 ω；返回图和坍塌图逐点固定全部内部自然数。 -/
theorem Gh_collapse_d.numbers_l {ω c X R N d Q T H B F j e V P U G : M.Domain}
    (hw : M.IsOmega ω) (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (h : Gh_collapse_d hZF ω c X N d Q T H B F j e V P U G) :
    ∃ hwB : M.mem ω B, (smdl_structure_l I (R := V) h.model.1.2.1).IsOmega ⟨ω,hwB⟩ ∧
      Rd_entry_d ω ω F ∧ ∀ n, M.mem n ω → Rd_entry_d n n F := by
  let C := smdl_structure_l I (R := V) h.model.1.2.1
  have native := ZFC.models_zf_l (h.theory.native_l I hZF hw)
  obtain ⟨w,natural,_⟩ := KPi.exists_omega_l (ZF.models_kpi_l native)
  have inj : Function.Injective (Subtype.val : C.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I h.model h.transitive
  have omega := image_omega_l (hEN := hZF.1) Subtype.val inj full native
    (fun _ ne => KP.mem_minimal_exists_d (ZF.modelsKP hZF) ne) natural
    (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D w.val)
  have eq : w.val = ω := hZF.1.eq_of_same_members w.val ω (fun n => ⟨omega.2 ω hw.1 n,hw.2 w.val omega.1 n⟩)
  have hwB : M.mem ω B := eq ▸ w.property
  have eq' : w = (⟨ω,hwB⟩ : C.Domain) := Subtype.ext eq
  exact ⟨hwB,eq' ▸ natural,(h.inverse_entries ω ω).mp
    (h.embedding.omega_l I hZF hw h.transitive trans h.model source hwB),
    fun n hn => (h.inverse_entries n n).mp
      (h.embedding.natural_l hZF hw h.transitive trans h.model source hwB n hn)⟩

end YesMetaZFC.Model.Forcing.Internal
