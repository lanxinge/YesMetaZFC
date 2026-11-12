import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.Model.Forcing.Order.ProductRight
import YesMetaZFC.Model.Forcing.Boolean.DenseMap
import YesMetaZFC.Model.Forcing.Collapse.ProductRealCollapse
import YesMetaZFC.Model.Forcing.Ground.ProductBlock
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.Model.Forcing.Collapse.PartialFunctionCertificate
import YesMetaZFC.Model.Forcing.Collapse.FiniteSequenceCertificate
import YesMetaZFC.Model.Forcing.Collapse.KripkeGeneric
import YesMetaZFC.Model.Forcing.TwoStep.ProductExtension
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable
import YesMetaZFC.Model.Forcing.Collapse.ProductTopTruth
import YesMetaZFC.Model.Forcing.Boolean.DensePushExtension
import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.Forcing.Boolean.ExtensionRealization
import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism
import YesMetaZFC.Model.Forcing.Boolean.DenseGround
import YesMetaZFC.Model.Forcing.Extension.Choice
import YesMetaZFC.Model.Forcing.Ground.RankRealNames

/-! # 全乘积与前缀乘尾部的实际稠密分解

尾条件把指定前缀固定为同一基块；与任意前缀拼接便得到全条件。
拼接图保持并反映序，像包含全部足够长条件，故在原全乘积中稠密。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

structure Ft_order_d (n b P D U : M.Domain) : Prop where
  conditions : ∀ p, M.mem p D ↔ M.mem p P ∧ M.IsRestrictionOf I b p n
  order : ∀ p q, Entry_d M p q U ↔ M.mem p D ∧ M.mem q D ∧ Fp_le_d I p q

theorem Ft_order_d.order_l {n b P D U : M.Domain} (tail : Ft_order_d hZF n b P D U) : Cond_order_d M D U D :=
  ⟨fun p hp => (tail.order p p).mpr ⟨hp,hp,Fp_le_d.refl_l I p⟩,
    fun p q r hp _ hr pq qr => (tail.order p r).mpr
      ⟨hp,hr,((tail.order p q).mp pq).2.2.trans_l I ((tail.order q r).mp qr).2.2⟩,
    fun p _ pD => (KP.mem_irrefl_d (ZF.modelsKP hZF) D ((tail.order p D).mp pD).2.1).elim⟩

theorem ft_order_l (n b P : M.Domain) : ∃ D U, Ft_order_d hZF n b P D U := by
  let ρ : Env M 2 := ⟨fun i => [b,n].get i,fun _ => n⟩
  let φ : UnarySchema 2 := { body := Formula.isRestriction kpair_convention_l (.bound 1) .newest (.bound 2) }
  have sat p : φ.denote ρ p ↔ M.IsRestrictionOf I b p n := Formula.satisfies_isRestriction_iff I ..
  obtain ⟨D,sep⟩ := ZF.separation_exists_d hZF φ ρ P
  let η : Env M 0 := ⟨Fin.elim0,fun _ => n⟩
  let ψ : BinarySchema 0 := { body := fp_le_m (𝒞 := kpair_convention_l) (.bound 1) .newest }
  obtain ⟨U,_,entries⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ η D
  exact ⟨D,U,fun p => (sep p).trans (and_congr_right fun _ => sat p),
    fun p q => (entries p q).trans (and_congr_right fun _ => and_congr_right fun _ => fp_le_sat_l I ..)⟩

theorem Fp_prefix_d.tail_factor_l {ω A n C S P R W : M.Domain}
    (stage : Fp_prefix_d hZF ω A n C S) (product : Fp_product_d hZF ω A P R)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (fa : M.IsSetFunctionFromTo I A ω W) :
    ∃ b D U J V F, M.mem b C ∧ (∀ q, M.mem q C → Entry_d M q b S) ∧ Ft_order_d hZF n b P D U ∧
      M.mem b D ∧ (∀ t, M.mem t D → Entry_d M t b U) ∧
      Prod_d hZF C S D U J V ∧ Cond_order_d M J V J ∧ M.IsSetFunctionFromTo I F J P ∧
      (∀ v p, Entry_d M v p F ↔ M.mem v J ∧ ∃ q t, KPair_d M v q t ∧ Ft_join_d n q t p) ∧
      Dmap_d J V J P R P F := by
  obtain ⟨b,hb,top⟩ := stage.top_l hZF hw hn fa
  have fb := (stage.conditions b).mp hb
  obtain ⟨D,U,tail⟩ := ft_order_l hZF n b P
  have hbP := (product.conditions b).mpr ⟨n,hn,fb⟩
  have hbD := (tail.conditions b).mpr ⟨hbP,fb.function.1,fun i s =>
    ⟨fun is => ⟨(fb.domain i).mpr ⟨s,is⟩,is⟩,And.right⟩⟩
  have tailTop t (ht : M.mem t D) : Entry_d M t b U :=
    (tail.order t b).mpr ⟨ht,hbD,fun i s is => ⟨s,(((tail.conditions t).mp ht).2.2 i s).mp is |>.2,fun _ h => h⟩⟩
  obtain ⟨J,V,pair,OP⟩ := product_order_l hZF (stage.order_l hZF) (tail.order_l hZF)
  have combine q (hq : M.mem q C) t (ht : M.mem t D) : ∃ p, M.mem p P ∧ Ft_join_d n q t p := by
    obtain ⟨tP,cut⟩ := (tail.conditions t).mp ht
    obtain ⟨m,hm,ft⟩ := (product.conditions t).mp tP
    obtain ⟨p,fp,joined⟩ := ft.join_l hZF ((stage.conditions q).mp hq) fb.domain cut
    exact ⟨p,(product.conditions p).mpr ⟨m,hm,fp⟩,joined⟩
  let ρ : Env M 1 := ⟨fun _ => n,fun _ => n⟩
  let φ : BinarySchema 1 := { body := set[3] ⟪∃ q t,
    ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 3)⌝ₛ,q,t) ∧
    ⌜ft_join_m⌝ₚ(⌜(.bound 2 : Term 3)⌝ₛ,q,t,⌜(.newest : Term 3)⌝ₛ)⟫ }
  have sat v p : φ.denote ρ v p ↔ ∃ q t, KPair_d M v q t ∧ Ft_join_d n q t p := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,ft_join_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨F,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := J) (target := P)
    (fun v hv => by
      obtain ⟨q,hq,t,ht,qt⟩ := (pair.pair v).mp hv
      obtain ⟨p,_,joined⟩ := combine q hq t ht
      exact ⟨p,(sat v p).mpr ⟨q,t,qt,joined⟩⟩)
    (fun v _ p p' hp hp' => by
      obtain ⟨q,t,qt,joined⟩ := (sat v p).mp hp
      obtain ⟨q',t',qt',joined'⟩ := (sat v p').mp hp'
      obtain ⟨rfl,rfl⟩ := kpair_injective_l M qt qt'
      exact joined.unique_l hZF.1 joined')
    (fun v p hv hp => by
      obtain ⟨q,t,qt,joined⟩ := (sat v p).mp hp
      obtain ⟨hq,ht⟩ := pair.components_l hZF hv qt
      obtain ⟨p',hp',joined'⟩ := combine q hq t ht
      exact (joined'.unique_l hZF.1 joined) ▸ hp')
  have graph v p := (values v p).trans (and_congr_right fun _ => sat v p)
  have mapped v v' p p' (vp : Entry_d M v p F) (vp' : Entry_d M v' p' F) :
      Entry_d M p p' R ↔ Entry_d M v v' V := by
    obtain ⟨hv,q,t,qt,joined⟩ := (graph v p).mp vp
    obtain ⟨hv',q',t',qt',joined'⟩ := (graph v' p').mp vp'
    obtain ⟨hq,ht⟩ := pair.components_l hZF hv qt
    obtain ⟨hq',ht'⟩ := pair.components_l hZF hv' qt'
    have le := joined.order_l hZF joined' ((stage.conditions q).mp hq).domain ((stage.conditions q').mp hq').domain
      ((tail.conditions t).mp ht).2 ((tail.conditions t').mp ht').2
    apply (product.order p p').trans
    apply Iff.trans (and_iff_right (fn.output_mem_of_pairMember vp))
    apply Iff.trans (and_iff_right (fn.output_mem_of_pairMember vp'))
    apply le.trans
    exact (and_congr ((stage.order q q').trans ⟨fun h => h.2.2,fun h => ⟨hq,hq',h⟩⟩).symm
      ((tail.order t t').trans ⟨fun h => h.2.2,fun h => ⟨ht,ht',h⟩⟩).symm).trans
        (pair.pair_order_l hZF hv hv' qt qt').symm
  have dense p (hp : M.mem p P) : ∃ v r, Entry_d M v r F ∧ Entry_d M r p R := by
    obtain ⟨m,hm,fp⟩ := (product.conditions p).mp hp
    have longer : ∃ k r, M.mem k ω ∧ Fp_at_d I ω A k r ∧ M.MemberSubset n k ∧ Fp_le_d I r p := by
      rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn m hm with eq | lt | gt
      · exact ⟨m,p,hm,fp,fun i hi => (eq i).mp hi,Fp_le_d.refl_l I p⟩
      · exact ⟨m,p,hm,fp,(hw.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive n lt,Fp_le_d.refl_l I p⟩
      · obtain ⟨r,fr,_,rp⟩ := fp.pad_l hZF hw hn fa ((hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive m gt)
        exact ⟨n,r,hn,fr,fun _ h => h,rp⟩
    obtain ⟨k,r,hk,fr,sub,rp⟩ := longer
    obtain ⟨q,t,fq,_,ft,cut,joined⟩ := fr.tail_split_l hZF fb sub
    have hq := (stage.conditions q).mpr fq
    have ht := (tail.conditions t).mpr ⟨(product.conditions t).mpr ⟨k,hk,ft⟩,cut⟩
    obtain ⟨v,qt⟩ := (I).total q t
    exact ⟨v,r,(graph v r).mpr ⟨(pair.pair v).mpr ⟨q,hq,t,ht,qt⟩,q,t,qt,joined⟩,
      (product.order r p).mpr ⟨(product.conditions r).mpr ⟨k,hk,fr⟩,hp,rp⟩⟩
  have nz {x B : M.Domain} (hx : M.mem x B) : x ≠ B := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hx)
  exact ⟨b,D,U,J,V,F,hb,top,tail,hbD,tailTop,pair,OP,fn,graph,
    dmap_of_order_l (product.order_l hZF) (fun v hv _ => (fn.2.2 v hv).imp fun _ h => h.2)
      (fun v p vp => ⟨⟨fn.input_mem_of_pairMember vp,nz (fn.input_mem_of_pairMember vp)⟩,
        fn.output_mem_of_pairMember vp,nz (fn.output_mem_of_pairMember vp)⟩) fn.1.2 mapped (fun p hp _ => dense p hp)⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 成员满包含保持整个有限支撑乘积及原前缀

先在原模型取统一的有限行空间。目标条件的每一行落在该空间的像中，
整个有限坐标块再由有限列回拉定理收回。因而条件空间没有新增条件，
不需要把秩模型的包含误当作完整初等嵌入。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (e : M.Domain → N.Domain) (inj : Function.Injective e)
  (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
include hM hN inj full

theorem fp_block_pull_l {ω A W : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (fa : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hM)) A ω W)
    {n p : N.Domain} (hn : N.mem n (e ω)) (block : Fp_at_d (kp_pair_l (ZF.modelsKP hN)) (e ω) (e A) n p) :
    ∃ k q, M.mem k ω ∧ Fp_at_d (kp_pair_l (ZF.modelsKP hM)) ω A k q ∧ e k = n ∧ e q = p := by
  obtain ⟨Z,union⟩ := KP.exists_union (ZF.modelsKP hM) W
  obtain ⟨S,rows⟩ := ZF.fseq_space_exists_l (kp_pair_l (ZF.modelsKP hM)) hM hw Z
  have rows' := image_fseq_l hM hN e inj full hw hw' rows
  have fa' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full fa
  have bounded : N.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hN)) p n (e S) := by
    refine ⟨block.function,block.domain,fun i hi => ?_⟩
    obtain ⟨s,is⟩ := (block.domain i).mp hi
    obtain ⟨κ,m,ia,hm,fs⟩ := block.coordinates i s is
    obtain ⟨κ₀,hκ₀,rfl⟩ := (full W κ).mp (fa'.output_mem_of_pairMember ia)
    have fs' : N.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hN)) s m (e Z) := by
      refine ⟨fs.1,fs.2.1,fun j hj => ?_⟩
      obtain ⟨a,ha,ja⟩ := fs.2.2 j hj
      obtain ⟨a₀,ha₀,rfl⟩ := (full κ₀ a).mp ha
      exact ⟨e a₀,(image_member_l e inj full).mpr ((union a₀).mpr ⟨κ₀,hκ₀,ha₀⟩),ja⟩
    exact ⟨s,(rows' s).mpr ⟨m,hm,fs'⟩,is⟩
  obtain ⟨k,q,hk,_,ek,eq⟩ := image_finite_function_pull_l hM hN e inj full hw hw' hn bounded
  exact ⟨k,q,hk,(image_fp_at_l (ZF.modelsKP hM) (ZF.modelsKP hN) e inj full).mpr (ek.symm ▸ eq.symm ▸ block),ek,eq⟩

private theorem fp_order_image_l {C S : M.Domain}
    (order : ∀ p q, Entry_d M p q S ↔ M.mem p C ∧ M.mem q C ∧ Fp_le_d (kp_pair_l (ZF.modelsKP hM)) p q) :
    ∀ p q, Entry_d N p q (e S) ↔ N.mem p (e C) ∧ N.mem q (e C) ∧ Fp_le_d (kp_pair_l (ZF.modelsKP hN)) p q := by
  intro p q
  constructor
  · intro pq
    obtain ⟨p₀,q₀,pq₀,rfl,rfl⟩ := image_entry_pull_l (ZF.modelsKP hM) hN.1 e inj full pq
    obtain ⟨hp,hq,le⟩ := (order p₀ q₀).mp pq₀
    exact ⟨(image_member_l e inj full).mpr hp,(image_member_l e inj full).mpr hq,
      (image_fp_le_l (ZF.modelsKP hM) (ZF.modelsKP hN) e inj full).mp le⟩
  · rintro ⟨hp,hq,le⟩
    obtain ⟨p₀,hp₀,rfl⟩ := (full C p).mp hp
    obtain ⟨q₀,hq₀,rfl⟩ := (full C q).mp hq
    exact (image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1 p₀ q₀ S).mp
      ((order p₀ q₀).mpr ⟨hp₀,hq₀,(image_fp_le_l (ZF.modelsKP hM) (ZF.modelsKP hN) e inj full).mpr le⟩)

theorem Fp_prefix_d.ground_image_l {ω A W n C S : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (fa : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hM)) A ω W) (hn : M.mem n ω)
    (stage : Fp_prefix_d hM ω A n C S) : Fp_prefix_d hN (e ω) (e A) (e n) (e C) (e S) := by
  refine ⟨fun p => ⟨?_,?_⟩,fp_order_image_l hM hN e inj full stage.order⟩
  · intro hp
    obtain ⟨q,hq,rfl⟩ := (full C p).mp hp
    exact (image_fp_at_l (ZF.modelsKP hM) (ZF.modelsKP hN) e inj full).mp ((stage.conditions q).mp hq)
  · intro block
    obtain ⟨k,q,hk,fq,ek,eq⟩ := fp_block_pull_l hM hN e inj full hw hw' fa ((image_member_l e inj full).mpr hn) block
    have kn := inj ek
    subst k
    exact (full C p).mpr ⟨q,(stage.conditions q).mpr fq,eq⟩

theorem Fp_product_d.ground_image_l {ω A W P R : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (fa : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hM)) A ω W)
    (product : Fp_product_d hM ω A P R) : Fp_product_d hN (e ω) (e A) (e P) (e R) := by
  refine ⟨fun p => ⟨?_,?_⟩,fp_order_image_l hM hN e inj full product.order⟩
  · intro hp
    obtain ⟨q,hq,rfl⟩ := (full P p).mp hp
    obtain ⟨n,hn,block⟩ := (product.conditions q).mp hq
    exact ⟨e n,(image_member_l e inj full).mpr hn,(image_fp_at_l (ZF.modelsKP hM) (ZF.modelsKP hN) e inj full).mp block⟩
  · rintro ⟨n,hn,block⟩
    obtain ⟨k,q,hk,fq,_,eq⟩ := fp_block_pull_l hM hN e inj full hw hw' fa hn block
    exact (full P p).mpr ⟨q,(product.conditions q).mpr ⟨k,hk,fq⟩,eq⟩

theorem Fp_stage_d.ground_image_l {ω A W n C S b : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (fa : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hM)) A ω W) (hn : M.mem n ω)
    (stage : Fp_stage_d hM ω A n C S b) : Fp_stage_d hN (e ω) (e A) (e n) (e C) (e S) (e b) := by
  refine ⟨stage.stage.ground_image_l hM hN e inj full hw hw' fa hn,?_,(image_member_l e inj full).mpr stage.member,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := (full S p).mp hp
    obtain ⟨a,d,pair⟩ := stage.relation q hq
    exact ⟨e a,e d,image_kpair_l e full pair⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := (full C p).mp hp
    exact (image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1 q b S).mp (stage.top q hq)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 积偏序继承右因子的实际满射坍缩

右坐标正则嵌入把真实泛型满射送入积扩张。其目标和定义域是成员满的
地参数像，满射性因而保持；有限公式反射给出每个原积条件上的力迫证书。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Prod_d.right_surjection_l {Q T P U C R b X Y : M.Domain} (product : Prod_d hZF Q T P U C R)
    (O : Cond_order_d M Q T Q) (L : Cond_order_d M P U P) (K : Cond_order_d M C R C)
    (hb : M.mem b Q) (top : ∀ q, M.mem q Q → Entry_d M q b T) (collapse : Psurj_d hZF P U P X Y)
    {G : M.Domain → Prop} (generic : Generic_d M C R C G)
    (j : M.Domain → (Internal.extension_l M hZF C R C G).Domain) (ground : ∀ x, Gval_d M C R C G x (j x)) :
    let E := Internal.extension_l M hZF C R C G
    let J := kpair_interpretation_l E (extension_ext_l K hZF generic) (internal_pair_l K hZF generic)
    ∃ f, E.IsSetFunctionFromTo J f (j X) (j Y) ∧ E.IsSetSurjectiveOnto J f (j X) (j Y) := by
  obtain ⟨H,small,e,inj,full,over⟩ := product.right_extension_l hZF O L K hb top generic
  let D := Internal.extension_l M hZF P U P H
  let E := Internal.extension_l M hZF C R C G
  have hD := preserves_zf_l L hZF small
  have hE := preserves_zf_l K hZF generic
  obtain ⟨a,ha⟩ := small.inhabited
  obtain ⟨k,checks,kfull,ki⟩ := check_map_l L hZF small ha
  have commute x : e (k x) = j x := (over x (k x)
    ((gval_check_map_l L hZF small ha k checks x (k x)).mpr rfl)).unique_l K hZF generic (ground x)
  obtain ⟨f,fn,onto⟩ := collapse.value_l hZF L small ha k ki kfull checks
  have image := image_function_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hE)) e inj full fn
  refine ⟨e f,?_,?_⟩
  · simpa only [commute] using image
  · intro y hy
    obtain ⟨v,hv,rfl⟩ := (full (k Y) y).mp ((commute Y).symm ▸ hy)
    obtain ⟨u,hu,uv⟩ := onto v hv
    exact ⟨e u,commute X ▸ (image_member_l e inj full).mpr hu,
      (image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hD)) hE.1 u v f).mp uv⟩

theorem Prod_d.right_collapses_l {Q T P U C R b X Y a : M.Domain} (product : Prod_d hZF Q T P U C R)
    (O : Cond_order_d M Q T Q) (L : Cond_order_d M P U P) (K : Cond_order_d M C R C)
    (hb : M.mem b Q) (top : ∀ q, M.mem q Q → Entry_d M q b T)
    (collapse : Psurj_d hZF P U P X Y) (ha : M.mem a C) : Collapses_d C R C a X Y := by
  obtain ⟨t,ct,nt,_⟩ := zf_check_l M hZF ha X
  obtain ⟨w,cw,nw,_⟩ := zf_check_l M hZF ha Y
  let φ : Formula 1 2 := .existsE coll_surj_s.body
  let α : Formula 1 12 :=
    .conj (cond_order_m (.bound 0) (.bound 1) (.bound 0))
    (.conj (cond_order_m (.bound 2) (.bound 3) (.bound 2))
    (.conj (prod_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5))
    (.conj (.mem (.bound 6) (.bound 0))
    (.conj (Formula.forallMem (.bound 0) (entry_m .newest (.bound 7) (.bound 2)))
    (.conj (psurj_m (.bound 2) (.bound 3) (.bound 2) (.bound 7) (.bound 8))
    (.conj (check_m (.bound 9) (.bound 7) (.bound 10)) (check_m (.bound 9) (.bound 8) (.bound 11))))))))
  have hα : α.FreeClosed := by simp -implicitDefEqProofs [α,Definitional.Formula.FreeClosed]
  have raw (N : Structure.{u}) (hN : N.Models ZF) (η : Env N 12) : Formula.satisfies η α ↔
      Cond_order_d N (η.bound 0) (η.bound 1) (η.bound 0) ∧ Cond_order_d N (η.bound 2) (η.bound 3) (η.bound 2) ∧
      Prod_d hN (η.bound 0) (η.bound 1) (η.bound 2) (η.bound 3) (η.bound 4) (η.bound 5) ∧ N.mem (η.bound 6) (η.bound 0) ∧
      (∀ q, N.mem q (η.bound 0) → Entry_d N q (η.bound 6) (η.bound 1)) ∧
      Psurj_d hN (η.bound 2) (η.bound 3) (η.bound 2) (η.bound 7) (η.bound 8) ∧
      Check_d N (η.bound 9) (η.bound 7) (η.bound 10) ∧ Check_d N (η.bound 9) (η.bound 8) (η.bound 11) := by
    simp only [α,Formula.satisfies_conj_iff,cond_order_sat_l hN.1,prod_sat_l hN,Formula.satisfies_mem_iff,
      Formula.satisfies_forallMem_iff,entry_sat_l N hN.1,psurj_sat_l hN,check_sat_l N hN.1]
    rfl
  let ρ : Env M 12 := ⟨fun i => [Q,T,P,U,C,R,b,X,Y,a,t,w].get i,fun _ => w⟩
  let v : Fin 2 → Term 12 := Fin.cases (.bound 10) (fun _ => .bound 11)
  have names : ∀ i, Name_d M C ((v i).eval ρ) := Fin.cases nt (fun _ => nw)
  have nz : a ≠ C := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ ha)
  have force := forces_of_generics_l φ coll_surj_s.freeClosed α hα v (.bound 4) (.bound 5) (.bound 4) (.bound 9)
    (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl (fun N hN η K _ _ _ truth G generic accepted ξ values => by
      obtain ⟨O,L,product,hb,top,collapse,ct,cw⟩ := (raw N hN η).mp truth
      obtain ⟨j,checks,_,_⟩ := check_map_l K hN generic accepted
      have ground x := (gval_check_map_l K hN generic accepted j checks x (j x)).mpr rfl
      obtain ⟨f,fn,onto⟩ := product.right_surjection_l hN O L K hb top collapse generic j ground
      have eX := qval_unique_l (checks _ _ ct) (values 0)
      have eY := qval_unique_l (checks _ _ cw) (values 1)
      apply (Formula.satisfies_exists_iff ξ coll_surj_s.body).mpr
      refine ⟨f,(Formula.satisfies_conj_iff (ξ.push f) fn_body_m onto_body_m).mpr ⟨?_,?_⟩⟩
      · exact (Formula.satisfies_isFunctionFromTo_iff _ (extension_ext_l K hN generic) (ξ.push f) .newest (.bound 1) (.bound 2)).mpr
          (eX ▸ eY ▸ fn)
      · exact (Formula.satisfies_isSurjectiveOnto_iff _ (ξ.push f) .newest (.bound 1) (.bound 2)).mpr (eX ▸ eY ▸ onto))
    hZF ρ K names ha nz ((raw M hZF ρ).mpr ⟨O,L,product,hb,top,collapse,ct,cw⟩)
  -- 显式比较两个闭环境，避免为逐槽等式展开整个力迫递归。
  let η : Env M 2 := ⟨Fin.cases t (fun _ => w),fun _ => w⟩
  have force' := (forces_env_l (B := C) (R := R) (z := C) hZF.1 φ coll_surj_s.freeClosed
    ⟨fun i => (v i).eval ρ,ρ.free⟩ η (Fin.cases rfl (fun _ => rfl)) a).mp force
  exact ⟨a,t,w,ha,K.refl a ha,ct,cw,force'⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 给定小泛型后的第一大坍缩吸收

先形成原小泛型与后一大坍缩的实际积泛型。积条件域受 κ 控制，右因子的
泛型满射给出原积的坍缩证书。Kripke 图因而产生原 Col(ω,κ) 的泛型，
其扩张与给定二步扩张保持全部地参数同构；不预设小泛型属于某个大扩张。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_pair_absorption_l {Q T P U b ω κ : M.Domain}
    (O : Cond_order_d M Q T Q) (L : Cond_order_d M P U P)
    (hw : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (size : M.CardinalLessOrEqual I Q κ)
    (space : Fseq_space_d I ω κ P)
    (order : ∀ p q, Entry_d M p q U ↔ M.mem p P ∧ M.mem q P ∧ M.MemberSubset q p)
    (top : ∀ q, M.mem q Q → Entry_d M q b T)
    {H : M.Domain → Prop} (small : Generic_d M Q T Q H) (hb : H b)
    (j : M.Domain → (Internal.extension_l M hZF Q T Q H).Domain)
    (checks : ∀ x t, Check_d M b x t → Qval_d M Q T Q H t (j x))
    {J : (Internal.extension_l M hZF Q T Q H).Domain}
    (same : ∀ x y, (Internal.extension_l M hZF Q T Q H).mem x (j P) → (Internal.extension_l M hZF Q T Q H).mem y (j P) →
      (Entry_d (Internal.extension_l M hZF Q T Q H) x y (j U) ↔ Entry_d (Internal.extension_l M hZF Q T Q H) x y J))
    (K : Cond_order_d (Internal.extension_l M hZF Q T Q H) (j P) J (j P))
    {G : (Internal.extension_l M hZF Q T Q H).Domain → Prop}
    (generic : Generic_d (Internal.extension_l M hZF Q T Q H) (j P) J (j P) G) :
    ∃ F : M.Domain → Prop, Generic_d M P U P F ∧
      Miso_over_d (Internal.extension_l M hZF P U P F)
        (Internal.extension_l (Internal.extension_l M hZF Q T Q H) (preserves_zf_l O hZF small) (j P) J (j P) G)
        (Gval_d M P U P F)
        (fun x => Gval_d (Internal.extension_l M hZF Q T Q H) (j P) J (j P) G (j x)) := by
  obtain ⟨C,R,product,OP⟩ := product_order_l hZF O L
  obtain ⟨g,iso⟩ := product.extension_l hZF O L OP top small hb j checks same K generic
  have infinite : M.IsInfiniteCardinal I ω κ :=
    ⟨hκ.1,ZF.exists_inclusionInjection hZF I (hκ.1.1.transitive ω hκ.2)⟩
  have large := ZF.fseq_bound_l I hZF hw infinite
    (ZF.exists_inclusionInjection hZF I (fun (x : M.Domain) (hx : M.mem x κ) => hx)) space
  have bound := ZF.infinite_product_l I hZF hw infinite size large product.pair
  obtain ⟨a,ha⟩ := g.inhabited
  have collapse := product.right_collapses_l hZF O L OP (small.proper b hb).1 top
    (fseq_psurj_l hZF hw space order ⟨ω,hκ.2⟩) (g.proper a ha).1
  obtain ⟨Γ,_,pulled,comparison⟩ := kripke_generic_l hZFC OP hw hκ bound space L order g ha collapse
  exact ⟨Pull_generic_d M Γ (Prod_generic_d hZF C j G),pulled,comparison.trans_l iso⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 给定前缀泛型与实际尾部泛型合成全乘积泛型

前缀扩张中的尾泛型产生积泛型，再由实际拼接图取像。
两向读取证明全泛型在原前缀上恰好等于给定滤子；扩张同构保留全部地参数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fp_prefix_d.tail_extension_l {ω A n C S P R W : M.Domain}
    (stage : Fp_prefix_d hZF ω A n C S) (product : Fp_product_d hZF ω A P R)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (fa : M.IsSetFunctionFromTo I A ω W)
    {H : M.Domain → Prop} (small : Generic_d M C S C H) :
    let E := Internal.extension_l M hZF C S C H
    let hE := preserves_zf_l (stage.order_l hZF) hZF small
    ∃ b D U, H b ∧ Ft_order_d hZF n b P D U ∧ M.mem b D ∧
      ∃ j : M.Domain → E.Domain, Function.Injective j ∧
        (∀ a y, E.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y) ∧
        (∀ x t, Check_d M b x t → Qval_d M C S C H t (j x)) ∧
        Cond_order_d E (j D) (j U) (j D) ∧
        ∀ G : E.Domain → Prop, Generic_d E (j D) (j U) (j D) G →
          ∃ K : M.Domain → Prop, Generic_d M P R P K ∧
            (∀ p, H p ↔ M.mem p C ∧ K p) ∧
            Miso_over_d (Internal.extension_l M hZF P R P K) (Internal.extension_l E hE (j D) (j U) (j D) G)
              (Gval_d M P R P K) (fun x => Gval_d E (j D) (j U) (j D) G (j x)) := by
  let E := Internal.extension_l M hZF C S C H
  have O := stage.order_l hZF
  have hE := preserves_zf_l O hZF small
  have L := product.order_l hZF
  obtain ⟨b,D,U,J,V,F,hb,top,tail,hbD,_,pair,OP,fn,graph,map⟩ := stage.tail_factor_l hZF product hw hn fa
  obtain ⟨a,ha⟩ := small.inhabited
  have accepted := small.upward a b ha hb (top a (small.proper a ha).1)
  obtain ⟨j,checks,full,inj⟩ := check_map_l O hZF small accepted
  have tailOrder := image_cond_order_l (ZF.modelsKP hZF) hE.1 j inj full (tail.order_l hZF)
  refine ⟨b,D,U,accepted,tail,hbD,j,inj,full,checks,tailOrder,fun G generic => ?_⟩
  obtain ⟨prodG,iso⟩ := pair.extension_l hZF O (tail.order_l hZF) OP top small accepted j checks
    (fun _ _ _ _ => Iff.rfl) tailOrder generic
  obtain ⟨o,empty,_⟩ := hw.1.1
  obtain ⟨ho,topP⟩ := product.empty_top_l hZF hw empty
  obtain ⟨whole,comparison⟩ := map.push_extension_l hZF OP L ho topP prodG
  let K := Push_generic_d P R F (Prod_generic_d hZF J j G)
  refine ⟨K,whole,?_,comparison.symm_l.trans_l iso⟩
  intro p
  constructor
  · intro hp
    have hpC := (small.proper p hp).1
    have hpP := (product.conditions p).mpr ⟨n,hn,(stage.conditions p).mp hpC⟩
    obtain ⟨t,gt⟩ := generic.inhabited
    obtain ⟨t,ht,rfl⟩ := (full D t).mp (generic.proper t gt).1
    obtain ⟨v,pt⟩ := (I).total p t
    have hv := (pair.pair v).mpr ⟨p,hpC,t,ht,pt⟩
    obtain ⟨r,hr,vr⟩ := fn.2.2 v hv
    obtain ⟨_,q,t',qt,joined⟩ := (graph v r).mp vr
    obtain ⟨eq,et⟩ := kpair_injective_l M qt pt
    subst q t'
    exact ⟨hpC,hpP,v,r,⟨hv,p,t,pt,hp,gt⟩,vr,(product.order r p).mpr
      ⟨hr,hpP,fun i s is => ⟨s,(joined.2 i s).mpr (Or.inl is),fun _ h => h⟩⟩⟩
  · rintro ⟨hpC,_,v,r,⟨_,q,t,qt,hq,_⟩,vr,rp⟩
    obtain ⟨_,q',t',qt',joined⟩ := (graph v r).mp vr
    obtain ⟨eq,et⟩ := kpair_injective_l M qt' qt
    subst q' t'
    have fq := (stage.conditions q).mp (small.proper q hq).1
    have cut := joined.prefix_l hZF fq.function.1 fq.domain
    have qp : Fp_le_d I q p := by
      intro i s is
      obtain ⟨t,it,st⟩ := ((product.order r p).mp rp).2.2 i s is
      exact ⟨t,(cut.2 i t).mpr ⟨((stage.conditions p).mp hpC).domain i |>.mpr ⟨s,is⟩,it⟩,st⟩
    exact small.upward q p hq hpC ((stage.order q p).mpr ⟨(small.proper q hq).1,hpC,qp⟩)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 首坐标吸收同时保留小扩张的全部原实数图

同一个大坍缩泛型服务所有小扩张实数。二步扩张同构把中间模型成员满地
嵌入该大扩张；完整函数图读取随之保持，最后才为同一商值取得大坍缩名字。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : Structure.{u}} (hZFC : M.Models ZFC) {V : Structure.{v}}
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem fseq_pair_real_l {Q T P U b ω α κ : M.Domain}
    (O : Cond_order_d M Q T Q) (L : Cond_order_d M P U P)
    (hw : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ)
    (smallSpace : Fseq_space_d I ω α Q) (bound : M.MemberSubset α κ)
    (space : Fseq_space_d I ω κ P)
    (order : ∀ p q, Entry_d M p q U ↔ M.mem p P ∧ M.mem q P ∧ M.MemberSubset q p)
    (top : ∀ q, M.mem q Q → Entry_d M q b T)
    {H : M.Domain → Prop} (small : Generic_d M Q T Q H) (hb : H b)
    (j : M.Domain → (Internal.extension_l M hZF Q T Q H).Domain)
    (checks : ∀ x t, Check_d M b x t → Qval_d M Q T Q H t (j x))
    {J : (Internal.extension_l M hZF Q T Q H).Domain}
    (same : ∀ x y, (Internal.extension_l M hZF Q T Q H).mem x (j P) → (Internal.extension_l M hZF Q T Q H).mem y (j P) →
      (Entry_d (Internal.extension_l M hZF Q T Q H) x y (j U) ↔ Entry_d (Internal.extension_l M hZF Q T Q H) x y J))
    (K : Cond_order_d (Internal.extension_l M hZF Q T Q H) (j P) J (j P))
    {G : (Internal.extension_l M hZF Q T Q H).Domain → Prop}
    (generic : Generic_d (Internal.extension_l M hZF Q T Q H) (j P) J (j P) G) :
    ∃ F : M.Domain → Prop, Generic_d M P U P F ∧
      Miso_over_d (Internal.extension_l M hZF P U P F)
        (Internal.extension_l (Internal.extension_l M hZF Q T Q H) (preserves_zf_l O hZF small) (j P) J (j P) G)
        (Gval_d M P U P F) (fun x => Gval_d (Internal.extension_l M hZF Q T Q H) (j P) J (j P) G (j x)) ∧
      ∃ i : (Internal.extension_l M hZF Q T Q H).Domain → (Internal.extension_l M hZF P U P F).Domain,
        Function.Injective i ∧ (∀ a y, y ∈ i a ↔ ∃ z, z ∈ a ∧ i z = y) ∧
        (∀ a, Gval_d M P U P F a (i (j a))) ∧
      ∀ k : M.Domain → V.Domain, ∀ τ x, Fn_value_d hZF k Q T Q ω τ H x →
        ∃ σ, Fn_value_d hZF k P U P ω σ F x := by
  have infinite : M.IsInfiniteCardinal I ω κ :=
    ⟨hκ.1,ZF.exists_inclusionInjection hZF I (hκ.1.1.transitive ω hκ.2)⟩
  have size := ZF.fseq_bound_l I hZF hw infinite (ZF.exists_inclusionInjection hZF I bound) smallSpace
  obtain ⟨F,genericF,iso⟩ := fseq_pair_absorption_l hZFC O L hw hκ size space order top small hb j checks same K generic
  let E := Internal.extension_l M hZF Q T Q H
  let D := Internal.extension_l M hZF P U P F
  have hE := preserves_zf_l O hZF small
  have hD := preserves_zf_l L hZF genericF
  obtain ⟨e,inj,full,fixed,_⟩ := iso.realize_l hE K generic hD.1
  have ground a : Gval_d M P U P F a (e (j a)) := (fixed a (e (j a))).mpr rfl
  refine ⟨F,genericF,iso,e,inj,full,ground,fun k τ x named => ?_⟩
  obtain ⟨j₀,y,_,base,fn,read⟩ := named
  have eq : j₀ = j := funext fun a => ((gval_check_map_l O hZF small hb j checks a (j₀ a)).mp (base a)).symm
  subst j₀
  obtain ⟨σ,_,value⟩ := value_name_l (e y)
  have function := fn0_of_function_l (ZF.modelsKP hD) (image_function_l e inj full (fn0_function_l (ZF.modelsKP hE) fn))
  exact ⟨σ,e ∘ j,e y,value,ground,function,read.image_l (KP.exists_pair (ZF.modelsKP hE)) hD.1 e inj full⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 第一大坍缩与主乘积第一前缀的实际识别

一个坐标块只保存零坐标上的有限序列。读取该行的集合图满射且保持、反映序，
故给定大坍缩泛型实际回拉成第一前缀泛型，同一扩张中的全部背景实数图保持。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Fp_prefix_d.first_map_l {ω A o one C S κ P U : M.Domain}
    (stage : Fp_prefix_d hZF ω A one C S) (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x o)
    (succ : M.SuccessorOf one o) (fa : M.IsSetFunction I A) (alphabet : Entry_d M o κ A)
    (space : Fseq_space_d I ω κ P) (L : Cond_order_d M P U P)
    (order : ∀ p q, Entry_d M p q U ↔ M.mem p P ∧ M.mem q P ∧ M.MemberSubset q p) :
    ∃ F, M.IsSetFunctionFromTo I F C P ∧
      (∀ c p, Entry_d M c p F ↔ M.mem c C ∧ Entry_d M o p c) ∧ Dmap_d C S C P U P F := by
  have oneMem i (hi : M.mem i one) : i = o :=
    ((succ i).mp hi).elim (fun h => (empty i h).elim) (hZF.1.eq_of_same_members i o)
  have row c (hc : M.mem c C) : ∃ p, M.mem p P ∧ Entry_d M o p c := by
    have fc := (stage.conditions c).mp hc
    obtain ⟨p,op⟩ := (fc.domain o).mp succ.predecessor_mem
    obtain ⟨α,n,oα,hn,fp⟩ := fc.coordinates o p op
    have eq := fa.2 o α κ oα alphabet
    exact ⟨p,(space p).mpr ⟨n,hn,eq ▸ fp⟩,op⟩
  let ρ : Env M 1 := ⟨fun _ => o,fun _ => o⟩
  let φ : BinarySchema 1 := { body := entry_m (.bound 2) .newest (.bound 1) }
  have sat c p : φ.denote ρ c p ↔ Entry_d M o p c := entry_sat_l M hZF.1 ..
  obtain ⟨F,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := P)
    (fun c hc => (row c hc).elim fun p hp => ⟨p,(sat c p).mpr hp.2⟩)
    (fun c hc p q hp hq => ((stage.conditions c).mp hc).function.2 o p q ((sat c p).mp hp) ((sat c q).mp hq))
    (fun c p hc hp => by
      obtain ⟨q,hq,oq⟩ := row c hc
      exact ((stage.conditions c).mp hc).function.2 o q p oq ((sat c p).mp hp) ▸ hq)
  have graph c p := (values c p).trans (and_congr_right fun _ => sat c p)
  have onto p (hp : M.mem p P) : ∃ c, Entry_d M c p F := by
    obtain ⟨o₀,empty₀,ho⟩ := hw.1.1
    have eq := hZF.1.eq_of_same_members o₀ o (fun z => iff_of_false (empty₀ z) (empty z))
    have zero : Fp_at_d I ω A o o := ⟨(Structure.IsSequenceOfLength.empty I empty).2.1,
      (Structure.IsSequenceOfLength.empty I empty).2.2,fun _ _ ⟨z,_,hz⟩ => (empty z hz).elim⟩
    obtain ⟨c,fc,last⟩ := zero.snoc_l hZF hw (eq ▸ ho) succ alphabet ((space p).mp hp)
    exact ⟨c,(graph c p).mpr ⟨(stage.conditions c).mpr fc,
      (last.entries_l I hZF.1 zero.domain o p).mpr (Or.inr ⟨rfl,rfl⟩)⟩⟩
  have nz {x B : M.Domain} (hx : M.mem x B) : x ≠ B := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hx)
  refine ⟨F,fn,graph,dmap_of_order_l L (fun c hc _ => (fn.2.2 c hc).imp fun _ h => h.2)
    (fun c p cp => ⟨⟨fn.input_mem_of_pairMember cp,nz (fn.input_mem_of_pairMember cp)⟩,
      fn.output_mem_of_pairMember cp,nz (fn.output_mem_of_pairMember cp)⟩) fn.1.2 ?_
    (fun p hp _ => (onto p hp).elim fun c cp => ⟨c,p,cp,L.refl p hp⟩)⟩
  intro c d p q cp dq
  obtain ⟨hc,op⟩ := (graph c p).mp cp
  obtain ⟨hd,oq⟩ := (graph d q).mp dq
  constructor
  · intro pq
    refine (stage.order c d).mpr ⟨hc,hd,fun i s is => ?_⟩
    have ei := oneMem i (((stage.conditions d).mp hd).domain i |>.mpr ⟨s,is⟩)
    subst i
    have es := ((stage.conditions d).mp hd).function.2 o s q is oq
    exact ⟨p,op,es.symm ▸ ((order p q).mp pq).2.2⟩
  · intro cd
    obtain ⟨r,or,qr⟩ := ((stage.order c d).mp cd).2.2 o q oq
    have eq := ((stage.conditions c).mp hc).function.2 o r p or op
    exact (order p q).mpr ⟨fn.output_mem_of_pairMember cp,fn.output_mem_of_pairMember dq,eq ▸ qr⟩

theorem Fp_prefix_d.first_generic_l {V : Structure.{v}} {ω A o one C S κ P U : M.Domain}
    (stage : Fp_prefix_d hZF ω A one C S) (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x o)
    (succ : M.SuccessorOf one o) (fa : M.IsSetFunction I A) (alphabet : Entry_d M o κ A)
    (space : Fseq_space_d I ω κ P) (L : Cond_order_d M P U P)
    (order : ∀ p q, Entry_d M p q U ↔ M.mem p P ∧ M.mem q P ∧ M.MemberSubset q p)
    {G : M.Domain → Prop} (generic : Generic_d M P U P G) :
    ∃ H : M.Domain → Prop, Generic_d M C S C H ∧
      Miso_over_d (Internal.extension_l M hZF C S C H) (Internal.extension_l M hZF P U P G) (Gval_d M C S C H) (Gval_d M P U P G) ∧
      ∀ k : M.Domain → V.Domain, ∀ τ x, Fn_value_d hZF k P U P ω τ G x → ∃ σ, Fn_value_d hZF k C S C ω σ H x := by
  obtain ⟨F,_,_,map⟩ := stage.first_map_l hZF hw empty succ fa alphabet space L order
  have O := stage.order_l hZF
  obtain ⟨p,hp⟩ := generic.inhabited
  have reg := map.regular_l L
  have hit := reg.dense_hit_l hZF L generic hp (fun q hq => map.dense q hq.1 hq.2.1)
  have small := reg_generic_l O L hZF reg generic hit
  have iso := map.ground_l hZF O L generic
  obtain ⟨e,member,inj,onto,over⟩ := iso.symm_l
  have full a y : y ∈ e a ↔ ∃ b, b ∈ a ∧ e b = y := by
    obtain ⟨b,rfl⟩ := onto y
    exact (member b a).symm.trans ⟨fun h => ⟨b,h,rfl⟩,fun ⟨c,h,eq⟩ => inj eq ▸ h⟩
  have hE := preserves_zf_l L hZF generic
  have hD := preserves_zf_l O hZF small
  refine ⟨Pull_generic_d M F G,small,iso,fun k τ x named => ?_⟩
  obtain ⟨j,y,_,ground,fn,read⟩ := named
  obtain ⟨σ,_,value⟩ := value_name_l (e y)
  exact ⟨σ,e ∘ j,e y,value,fun a => (over a (j a)).mp (ground a),
    fn0_of_function_l (ZF.modelsKP hD) (image_function_l e inj full (fn0_function_l (ZF.modelsKP hE) fn)),
    read.image_l (KP.exists_pair (ZF.modelsKP hE)) hD.1 e inj full⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 保留前缀的全泛型逐名字吸收原实数

前缀限制的精确方程允许沿原正则包含使用同一个名字 τ。
完整背景图保持，并证明该名字的实际商值属于规范有限前缀实数并。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : Structure.{u}} (hZF : M.Models ZF) {V : Structure.{v}}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Fp_prefix_d.named_real_l {ω A n C S P R W τ : M.Domain} {H G : M.Domain → Prop}
    (stage : Fp_prefix_d hZF ω A n C S) (product : Fp_product_d hZF ω A P R)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (fa : M.IsSetFunctionFromTo I A ω W)
    (generic : Generic_d M P R P G) (same : ∀ p, H p ↔ M.mem p C ∧ G p)
    (k : M.Domain → V.Domain) {x : V.Domain} (named : Fn_value_d hZF k C S C ω τ H x) :
    Fn_value_d hZF k P R P ω τ G x ∧
      ∀ y : (Internal.extension_l M hZF P R P G).Domain, Qval_d M P R P G τ y → Rp_value_d hZF ω A P R G y := by
  have eq : H = (fun p => M.mem p C ∧ G p) := funext fun p => propext (same p)
  subst H
  obtain ⟨j,y,value,ground,fn,read⟩ := named
  obtain ⟨small,e,inj,full,values,over⟩ := stage.extension_l hZF product hw hn fa generic
  have hE := preserves_zf_l (stage.order_l hZF) hZF small
  have hD := preserves_zf_l (product.order_l hZF) hZF generic
  have target := values y τ value
  have real := stage.real_value_l hZF hw hn fa product generic j ground value target fn
  exact ⟨⟨e ∘ j,e y,target,fun a => over a (j a) (ground a),
    fn0_of_function_l (ZF.modelsKP hD) (image_function_l e inj full (fn0_function_l (ZF.modelsKP hE) fn)),
    read.image_l (KP.exists_pair (ZF.modelsKP hE)) hD.1 e inj full⟩,
    fun y value => qval_unique_l target value ▸ real⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 反射后实际构造保留给定前缀的完整乘积泛型

先枚举前缀扩张的名字商，再由原泛型工厂在尾偏序中构造泛型。
拼接得到全泛型，前缀的每个实数名字仍解释同一背景图并进入规范实数并。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : Structure.{u}} (hZF : M.Models ZF) {V : Structure.{v}}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Fp_prefix_d.countable_extend_l {ω A n C S P R W : M.Domain}
    (stage : Fp_prefix_d hZF ω A n C S) (product : Fp_product_d hZF ω A P R)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (fa : M.IsSetFunctionFromTo I A ω W)
    (s : Nat → M.Domain) (onto : Function.Surjective s) {H : M.Domain → Prop}
    (small : Generic_d M C S C H) :
    ∃ G : M.Domain → Prop, Generic_d M P R P G ∧ (∀ p, H p ↔ M.mem p C ∧ G p) ∧
      ∀ k : M.Domain → V.Domain, ∀ τ x, Fn_value_d hZF k C S C ω τ H x →
        Fn_value_d hZF k P R P ω τ G x ∧
          ∀ y : (Internal.extension_l M hZF P R P G).Domain, Qval_d M P R P G τ y → Rp_value_d hZF ω A P R G y := by
  let E := Internal.extension_l M hZF C S C H
  have hE := preserves_zf_l (stage.order_l hZF) hZF small
  obtain ⟨b,D,U,_,_,hb,j,inj,full,_,O,compose⟩ := stage.tail_extension_l hZF product hw hn fa small
  obtain ⟨e,enum⟩ := extension_countable_l hZF (B := C) (R := S) (z := C) (G := H) s onto
  have positive : E.mem (j b) (j D) := (image_member_l j inj full).mpr hb
  have nz : j b ≠ j D := fun eq => KP.mem_irrefl_d (ZF.modelsKP hE) (j D) (eq ▸ positive)
  obtain ⟨K,generic,_⟩ := internal_generic_l O e enum positive nz
  obtain ⟨G,g,keep,_⟩ := compose K generic
  exact ⟨G,g,keep,fun k τ x named => stage.named_real_l hZF product hw hn fa g keep k (τ := τ) (x := x) named⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 小坍缩的全部实数实际进入同一主乘积的规范实数并

在反射后的外部可数源中，先于原小扩张内构造第一大坍缩泛型，再吸收为
原大坍缩，识别第一前缀并实际补齐尾部。所有原小扩张实数共用这一全泛型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : Structure.{u}} (hZFC : M.Models ZFC) {V : Structure.{v}}
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Fp_product_d.countable_absorb_l {ω A P R W o κ α Q T : M.Domain}
    (product : Fp_product_d hZF ω A P R) (hw : M.IsOmega ω) (fa : M.IsSetFunctionFromTo I A ω W)
    (empty : ∀ x, ¬ M.mem x o) (alphabet : Entry_d M o κ A) (hκ : M.IsUncountableCardinal I ω κ)
    (smallSpace : Fseq_space_d I ω α Q) (bound : M.MemberSubset α κ)
    (O : Cond_order_d M Q T Q)
    (smallOrder : ∀ p q, Entry_d M p q T ↔ M.mem p Q ∧ M.mem q Q ∧ M.MemberSubset q p)
    (s : Nat → M.Domain) (onto : Function.Surjective s) {H : M.Domain → Prop} (small : Generic_d M Q T Q H) :
    ∃ G : M.Domain → Prop, Generic_d M P R P G ∧
      ∃ ι : (Internal.extension_l M hZF Q T Q H).Domain → (Internal.extension_l M hZF P R P G).Domain,
        Function.Injective ι ∧ (∀ a y, y ∈ ι a ↔ ∃ z, z ∈ a ∧ ι z = y) ∧
        (∀ a y, Gval_d M Q T Q H a y → Gval_d M P R P G a (ι y)) ∧
        (∀ ν, Gval_d M Q T Q H ω ν → ∀ x, Fn0_d ν ν x → Rp_value_d hZF ω A P R G (ι x)) ∧
      ∀ k : M.Domain → V.Domain, ∀ τ x, Fn_value_d hZF k Q T Q ω τ H x →
        ∃ σ, Fn_value_d hZF k P R P ω σ G x ∧
          ∀ y : (Internal.extension_l M hZF P R P G).Domain, Qval_d M P R P G σ y → Rp_value_d hZF ω A P R G y := by
  obtain ⟨o₀,empty₀,ho₀⟩ := hw.1.1
  have ho : M.mem o ω := (hZF.1.eq_of_same_members o₀ o (fun x => iff_of_false (empty₀ x) (empty x))) ▸ ho₀
  have zero (Y : M.Domain) : M.IsSetFunctionFromTo I o o Y :=
    ⟨(Structure.IsSequenceOfLength.empty I empty).2.1,(Structure.IsSequenceOfLength.empty I empty).2.2,
      fun x hx => (empty x hx).elim⟩
  have hoQ := (smallSpace o).mpr ⟨o,ho,zero α⟩
  have top q (hq : M.mem q Q) : Entry_d M q o T := (smallOrder q o).mpr ⟨hq,hoQ,fun x hx => (empty x hx).elim⟩
  obtain ⟨a,ha⟩ := small.inhabited
  have accepted := small.upward a o ha hoQ (top a (small.proper a ha).1)
  obtain ⟨B,U,space,L,order⟩ := fseq_collapse_order_l hZF hw κ
  obtain ⟨j,checks,full,inj⟩ := check_map_l O hZF small accepted
  let E := Internal.extension_l M hZF Q T Q H
  have hE := preserves_zf_l O hZF small
  have oldOrder := image_cond_order_l (ZF.modelsKP hZF) hE.1 j inj full L
  obtain ⟨e,enum⟩ := extension_countable_l hZF (B := Q) (R := T) (z := Q) (G := H) s onto
  have positive : E.mem (j o) (j B) := (image_member_l j inj full).mpr ((space o).mpr ⟨o,ho,zero κ⟩)
  obtain ⟨K,big,_⟩ := internal_generic_l oldOrder e enum positive
    (fun eq => KP.mem_irrefl_d (ZF.modelsKP hE) (j B) (eq ▸ positive))
  obtain ⟨F,genericF,_,i₁,inj₁,full₁,ground₁,firstReals⟩ := fseq_pair_real_l hZFC (V := V) O L hw hκ smallSpace bound space order top small accepted
    j checks (fun _ _ _ _ => Iff.rfl) oldOrder big
  obtain ⟨one,succ,hOne⟩ := hw.1.2 o ho
  obtain ⟨C,S,stage⟩ := product.prefix_l hZF hOne
  obtain ⟨J,first,firstIso,prefixReals⟩ := stage.first_generic_l hZF (V := V) hw empty succ fa.1 alphabet space L order genericF
  obtain ⟨G,whole,keep,allReals⟩ := stage.countable_extend_l hZF (V := V) product hw hOne fa s onto first
  obtain ⟨i₂,mem₂,inj₂,onto₂,ground₂⟩ := firstIso.symm_l
  have full₂ a y : y ∈ i₂ a ↔ ∃ z, z ∈ a ∧ i₂ z = y := by
    obtain ⟨z,rfl⟩ := onto₂ y
    exact (mem₂ z a).symm.trans ⟨fun h => ⟨z,h,rfl⟩,fun ⟨w,h,eq⟩ => inj₂ eq ▸ h⟩
  have eq : (fun p => M.mem p C ∧ G p) = J := funext fun p => propext (keep p).symm
  have lift := stage.extension_l hZF product hw hOne fa whole
  rw [eq] at lift
  obtain ⟨_,i₃,inj₃,full₃,values₃,ground₃⟩ := lift
  let ι := i₃ ∘ i₂ ∘ i₁
  have covers a y : y ∈ ι a ↔ ∃ z, z ∈ a ∧ ι z = y := by
    constructor
    · intro hy
      obtain ⟨b,hb,rfl⟩ := (full₃ (i₂ (i₁ a)) y).mp hy
      obtain ⟨c,hc,rfl⟩ := (full₂ (i₁ a) b).mp hb
      obtain ⟨z,hz,rfl⟩ := (full₁ a c).mp hc
      exact ⟨z,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact (full₃ _ _).mpr ⟨i₂ (i₁ z),(full₂ _ _).mpr ⟨i₁ z,(full₁ a (i₁ z)).mpr ⟨z,hz,rfl⟩,rfl⟩,rfl⟩
  have fixed a y (hy : Gval_d M Q T Q H a y) : Gval_d M P R P G a (ι y) := by
    have eq := (gval_check_map_l O hZF small accepted j checks a y).mp hy
    subst y
    exact ground₃ a _ ((ground₂ a _).mp (ground₁ a))
  have capture ν (baseω : Gval_d M Q T Q H ω ν) x (fn : Fn0_d ν ν x) : Rp_value_d hZF ω A P R G (ι x) := by
    have eqν := (gval_check_map_l O hZF small accepted j checks ω ν).mp baseω
    subst ν
    have hF := preserves_zf_l L hZF genericF
    have hJ := preserves_zf_l (stage.order_l hZF) hZF first
    have fn₁ := fn0_of_function_l (ZF.modelsKP hF)
      (image_function_l i₁ inj₁ full₁ (fn0_function_l (ZF.modelsKP hE) fn))
    have fn₂ := fn0_of_function_l (ZF.modelsKP hJ)
      (image_function_l i₂ inj₂ full₂ (fn0_function_l (ZF.modelsKP hF) fn₁))
    obtain ⟨τ,_,value⟩ := value_name_l (i₂ (i₁ x))
    have enter := stage.real_value_l (τ := τ) hZF hw hOne fa product whole
    rw [eq] at enter
    exact enter (i₂ ∘ i₁ ∘ j) (fun a => (ground₂ a _).mp (ground₁ a)) value (values₃ _ τ value) fn₂
  refine ⟨G,whole,ι,inj₃.comp (inj₂.comp inj₁),covers,fixed,capture,fun k τ x named => ?_⟩
  obtain ⟨τ₁,named₁⟩ := firstReals k τ x named
  obtain ⟨τ₂,named₂⟩ := prefixReals k τ₁ x named₁
  exact ⟨τ₂,allReals k τ₂ x named₂⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原 R* 实数沿同一泛型提升到背景 R*

任取其实际有限前缀表示，在该前缀中把实数规范化为检查子集名字。
同一个名字在目标前缀中实际求值，随后两侧各自进入原全扩张。
两个包含都固定地参数，故完整实数图在同一地坐标下对应。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (e : M.Domain → N.Domain) (inj : Function.Injective e)
  (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
include inj full

theorem Rp_value_d.ground_image_l {ω A W P R : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (fa : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hM)) A ω W) (product : Fp_product_d hM ω A P R)
    {G : M.Domain → Prop} {H : N.Domain → Prop}
    (g : Generic_d M P R P G) (h : Generic_d N (e P) (e R) (e P) H) (same : ∀ p, G p ↔ H (e p))
    (j : M.Domain → (Internal.extension_l M hM P R P G).Domain) (base : ∀ a, Gval_d M P R P G a (j a))
    (k : N.Domain → (Internal.extension_l N hN (e P) (e R) (e P) H).Domain)
    (ground : ∀ a, Gval_d N (e P) (e R) (e P) H a (k a))
    {x : (Internal.extension_l M hM P R P G).Domain} (real : Rp_value_d hM ω A P R G x) :
    ∃ y, Rp_value_d hN (e ω) (e A) (e P) (e R) H y ∧ Fn_read_d (k ∘ e) j x y := by
  have product' := product.ground_image_l hM hN e inj full hw hw' fa
  have fa' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full fa
  have hE := preserves_zf_l (product.order_l hM) hM g
  obtain ⟨n,C,S,b,hn,stage,j₀,base₀,τ,z,vz,vx,fz⟩ := real
  have stage' := stage.ground_image_l hM hN e inj full hw hw' fa hn
  have hn' := (image_member_l e inj full).mpr hn
  obtain ⟨small,f,fi,ff,values,over⟩ := stage.stage.extension_l hM product hw hn fa g
  obtain ⟨small',f',_,ff',values',over'⟩ := stage'.stage.extension_l hN product' hw' hn' fa' h
  have hD := preserves_zf_l (stage.stage.order_l hM) hM small
  have hD' := preserves_zf_l (stage'.stage.order_l hN) hN small'
  obtain ⟨p,hp⟩ := small'.inhabited
  obtain ⟨l,checks,_,_⟩ := check_map_l (stage'.stage.order_l hN) hN small' hp
  have base' a := (gval_check_map_l (stage'.stage.order_l hN) hN small' hp l checks a (l a)).mpr rfl
  have same' p : (M.mem p C ∧ G p) ↔ (N.mem (e p) (e C) ∧ H (e p)) :=
    and_congr (image_member_l e inj full).symm (same p)
  obtain ⟨σ,y,_,vy,fy,read⟩ := check_real_image_l hM hN e inj full (stage.stage.order_l hM) small small' same' j₀ base₀ l base' fz
  have moved := (read.image_l (KP.exists_pair (ZF.modelsKP hD)) hE.1 f fi ff).background_image_l f' ff'
    (fn0_function_l (ZF.modelsKP hD') fy).1.1
  have left : f ∘ j₀ = j := funext fun a => (over a (j₀ a) (base₀ a)).unique_l (product.order_l hM) hM g (base a)
  have right : f' ∘ (l ∘ e) = k ∘ e := funext fun a =>
    (over' (e a) (l (e a)) (base' (e a))).unique_l (product'.order_l hN) hN h (ground (e a))
  have ex : f z = x := qval_unique_l (values z τ vz) vx
  rw [left,right,ex] at moved
  exact ⟨f' y,stage'.stage.real_value_l hN hw' hn' fa' product' h l base' vy (values' y (e σ) vy) fy,moved⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 每个背景前缀实数由原秩模型同一前缀的名字读出

有限长度由原 ω 回拉，规范前缀的唯一性再识别条件域、顺序和最大条件。
在这一实际原前缀中规范化名字，然后沿原模型自己的前缀包含进入全扩张。
完整背景实数图与原泛型始终不变，所得值确在原模型的 R* 中。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {c X R θ : M.Domain}
  (source : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (trans : M.TransitiveSet X)
  (rank : V_d (kp_pair_l (ZF.modelsKP hZF)) θ X)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).Models ZF)
include trans rank

theorem Smem_d.product_real_names_l
    {ω A P T W : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).Domain}
    (hw : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).IsOmega ω)
    (fa : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP native)) A ω W) (product : Fp_product_d native ω A P T)
    {H : M.Domain → Prop} (generic : Generic_d M P.val T.val P.val H)
    (j : M.Domain → (Internal.extension_l M hZF P.val T.val P.val H).Domain)
    (ground : ∀ a, Gval_d M P.val T.val P.val H a (j a)) :
    let N := smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1
    let G : N.Domain → Prop := H ∘ Subtype.val
    Generic_d N P T P G ∧ ∀ x, Rp_value_d hZF ω.val A.val P.val T.val H x →
      ∃ τ, Fn_value_d native (j ∘ Subtype.val) P T P ω τ G x ∧
        ∀ y, Qval_d N P T P G τ y → Rp_value_d native ω A P T G y := by
  let N := smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1
  let E := Internal.extension_l M hZF P.val T.val P.val H
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l (kp_pair_l (ZF.modelsKP hZF)) source trans
  have hw' : M.IsOmega ω.val := image_omega_l (hEN := hZF.1) Subtype.val inj full native
    (fun _ => KP.mem_minimal_exists_d (ZF.modelsKP hZF)) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D ω.val)
  have fa' := image_function_l (hEN := hZF.1) (hPN := KP.exists_pair (ZF.modelsKP hZF)) Subtype.val inj full fa
  have product' := product.ground_image_l native hZF Subtype.val inj full hw hw' fa
  have g := generic.ground_pull_l (ZF.modelsKP native) hZF.1 Subtype.val inj full
  have hE := preserves_zf_l (product'.order_l hZF) hZF generic
  refine ⟨g,fun x real => ?_⟩
  obtain ⟨n,C,S,b,hn,stage,k,base,τ,y,value,target,fy⟩ := real
  -- 规范前缀唯一性同时固定条件域、顺序和顶条件。
  obtain ⟨n₀,hn₀,rfl⟩ := (full ω n).mp hn
  obtain ⟨C₀,S₀,b₀,stage₀⟩ := product.stage_l native hw hn₀ fa
  obtain ⟨ec,es,eb⟩ := (stage₀.ground_image_l native hZF Subtype.val inj full hw hw' fa hn₀).unique_l hZF stage
  subst C S b
  obtain ⟨small,f,fi,ff,keep,over⟩ := stage.stage.extension_l hZF product' hw' hn fa' generic
  let D := Internal.extension_l M hZF C₀.val S₀.val C₀.val (fun p => M.mem p C₀.val ∧ H p)
  have hD := preserves_zf_l (stage.stage.order_l hZF) hZF small
  have commute a : f (k a) = j a :=
    (over a (k a) (base a)).unique_l (product'.order_l hZF) hZF generic (ground a)
  have same : f y = x := qval_unique_l (keep y τ value) target
  obtain ⟨q,hq⟩ := small.inhabited
  obtain ⟨k₀,kc,kf,_⟩ := check_map_l (stage.stage.order_l hZF) hZF small hq
  have eqk : k₀ = k := funext fun a => (gval_check_map_l (stage.stage.order_l hZF) hZF small hq k₀ kc a (k a)).mp (base a)
  subst k₀
  -- 先在背景前缀读取全扩张中的同一个 x，再把规范名字收回原秩层。
  have named : Fn_value_d hZF j C₀.val S₀.val C₀.val ω.val τ (fun p => M.mem p C₀.val ∧ H p) x := by
    refine ⟨k,y,value,base,fy,fun a d => ⟨?_,?_⟩⟩
    · intro ad
      obtain ⟨a₀,d₀,edge,rfl,rfl⟩ := (image_entries_l f ff (fn0_function_l (ZF.modelsKP hD) fy).1.1 a d).mp (same.symm ▸ ad)
      obtain ⟨a₁,_,rfl⟩ := (kf ω.val a₀).mp (fy.bound_l edge).1
      obtain ⟨d₁,_,rfl⟩ := (kf ω.val d₀).mp (fy.bound_l edge).2
      exact ⟨a₁,d₁,(commute a₁).symm,(commute d₁).symm,edge⟩
    · rintro ⟨a₀,d₀,rfl,rfl,edge⟩
      have moved := (image_entry_iff_l f fi ff (KP.exists_pair (ZF.modelsKP hD)) hE.1 (k a₀) (k d₀) y).mp edge
      simpa only [commute,same] using moved
  obtain ⟨σ,old⟩ := Smem_d.check_real_value_l hZF source trans rank native (stage₀.stage.order_l native) small named
  -- 原模型内的正则前缀包含保留已选定的规范名字。
  have restriction p : ((fun q => M.mem q C₀.val ∧ H q) ∘ (Subtype.val : N.Domain → M.Domain)) p ↔
      N.mem p C₀ ∧ (H ∘ Subtype.val) p := and_congr (image_member_l (M := N) (N := M) Subtype.val inj full) Iff.rfl
  exact ⟨σ,stage₀.stage.named_real_l native product hw hn₀ fa g restriction (j ∘ Subtype.val) old⟩

/-- 原、背景两个 R* 通过完整实数图双向对应，且共用给定的全泛型。 -/
theorem Smem_d.product_reals_l
    {ω A P T W : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).Domain}
    (hw : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).IsOmega ω)
    (fa : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP native)) A ω W) (product : Fp_product_d native ω A P T)
    {H : M.Domain → Prop} (generic : Generic_d M P.val T.val P.val H)
    (j : M.Domain → (Internal.extension_l M hZF P.val T.val P.val H).Domain)
    (ground : ∀ a, Gval_d M P.val T.val P.val H a (j a)) :
    let N := smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1
    let G : N.Domain → Prop := H ∘ Subtype.val
    ∃ l : N.Domain → (Internal.extension_l N native P T P G).Domain,
      (∀ a, Gval_d N P T P G a (l a)) ∧
      (∀ y, Rp_value_d native ω A P T G y →
        ∃ x, Rp_value_d hZF ω.val A.val P.val T.val H x ∧ Fn_read_d (j ∘ Subtype.val) l y x) ∧
      ∀ x, Fn0_d (j ω.val) (j ω.val) x →
        (Rp_value_d hZF ω.val A.val P.val T.val H x ↔
          ∃ y, Rp_value_d native ω A P T G y ∧ Fn_read_d (j ∘ Subtype.val) l y x) := by
  let N := smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l (kp_pair_l (ZF.modelsKP hZF)) source trans
  have hw' : M.IsOmega ω.val := image_omega_l (hEN := hZF.1) Subtype.val inj full native
    (fun _ => KP.mem_minimal_exists_d (ZF.modelsKP hZF)) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D ω.val)
  have product' := product.ground_image_l native hZF Subtype.val inj full hw hw' fa
  have fa' := image_function_l (hEN := hZF.1) (hPN := KP.exists_pair (ZF.modelsKP hZF)) Subtype.val inj full fa
  have hE := preserves_zf_l (product'.order_l hZF) hZF generic
  obtain ⟨g,names⟩ := Smem_d.product_real_names_l hZF source trans rank native hw fa product generic j ground
  obtain ⟨b,hb⟩ := g.inhabited
  obtain ⟨l,checks,_,_⟩ := check_map_l (product.order_l native) native g hb
  have base a := (gval_check_map_l (product.order_l native) native g hb l checks a (l a)).mpr rfl
  have forward y (real : Rp_value_d native ω A P T (H ∘ Subtype.val) y) :=
    real.ground_image_l native hZF Subtype.val inj full hw hw' fa product g generic (fun _ => Iff.rfl) l base j ground
  refine ⟨l,base,forward,fun x fx => ⟨?_,?_⟩⟩
  · intro real
    obtain ⟨τ,⟨l₀,y,value,base₀,_,read⟩,old⟩ := names x real
    have eq : l₀ = l := funext fun a => (base₀ a).unique_l (product.order_l native) native g (base a)
    subst l₀
    exact ⟨y,old y value,read⟩
  · rintro ⟨y,real,read⟩
    obtain ⟨z,rz,read'⟩ := forward y real
    have fz := rz.function_l hZF hw' fa' product' generic j ground
    have eq := read.unique_l (ZF.modelsKP hE) read' (fn0_function_l (ZF.modelsKP hE) fx).1.1
      (fn0_function_l (ZF.modelsKP hE) fz).1.1
    exact eq.symm ▸ rz

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同一小坍缩吸收运行中的原秩模型实数名字

先识别原乘积的背景呈示，再完成第一坐标吸收及尾部泛型构造。
同一个全泛型和同一个成员满嵌入同时覆盖全部小扩张实数；每个像实数
随后由原秩模型中的实际名字解释，其原商值属于本次运行的原 R*。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC

theorem Smem_d.countable_absorb_names_l {c X R θ : M.Domain}
    (source : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (trans : M.TransitiveSet X)
    (rank : V_d (kp_pair_l (ZF.modelsKP hZF)) θ X)
    (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).Models ZF)
    {ω A P T W o κ : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).Domain}
    (hw : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).IsOmega ω)
    (fa : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP native)) A ω W) (product : Fp_product_d native ω A P T)
    (empty : ∀ x, ¬ (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).mem x o)
    (alphabet : Entry_d (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1) o κ A)
    (hκ : M.IsUncountableCardinal (kp_pair_l (ZF.modelsKP hZF)) ω.val κ.val)
    {α Q S : M.Domain} (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω.val α Q)
    (bound : M.MemberSubset α κ.val) (O : Cond_order_d M Q S Q)
    (order : ∀ p q, Entry_d M p q S ↔ M.mem p Q ∧ M.mem q Q ∧ M.MemberSubset q p)
    (s : Nat → M.Domain) (onto : Function.Surjective s) {H : M.Domain → Prop}
    (small : Generic_d M Q S Q H) :
    ∃ G, Generic_d M P.val T.val P.val G ∧
      ∃ ι : (Internal.extension_l M hZF Q S Q H).Domain → (Internal.extension_l M hZF P.val T.val P.val G).Domain,
        Function.Injective ι ∧ (∀ a y, y ∈ ι a ↔ ∃ z, z ∈ a ∧ ι z = y) ∧
        (∀ a y, Gval_d M Q S Q H a y → Gval_d M P.val T.val P.val G a (ι y)) ∧
      ∃ j : M.Domain → (Internal.extension_l M hZF P.val T.val P.val G).Domain,
        (∀ a, Gval_d M P.val T.val P.val G a (j a)) ∧
        ∀ ν, Gval_d M Q S Q H ω.val ν → ∀ x, Fn0_d ν ν x →
          Rp_value_d hZF ω.val A.val P.val T.val G (ι x) ∧
          ∃ τ, Fn_value_d native (j ∘ Subtype.val) P T P ω τ (G ∘ Subtype.val) (ι x) ∧
            ∀ y, Qval_d (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1)
              P T P (G ∘ Subtype.val) τ y → Rp_value_d native ω A P T (G ∘ Subtype.val) y := by
  let N := smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l (kp_pair_l (ZF.modelsKP hZF)) source trans
  have hw' : M.IsOmega ω.val := image_omega_l (hEN := hZF.1) Subtype.val inj full native
    (fun _ => KP.mem_minimal_exists_d (ZF.modelsKP hZF)) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D ω.val)
  have product' := product.ground_image_l native hZF Subtype.val inj full hw hw' fa
  have fa' := image_function_l (hEN := hZF.1) (hPN := KP.exists_pair (ZF.modelsKP hZF)) Subtype.val inj full fa
  have empty' x (hx : M.mem x o.val) : False := (full o x).mp hx |>.elim fun y hy => empty y hy.1
  have alphabet' := (image_entry_iff_l (M := N) (N := M) Subtype.val inj full
    (KP.exists_pair (ZF.modelsKP native)) hZF.1 o κ A).mp alphabet
  obtain ⟨G,g,ι,ii,ifull,over,capture,_⟩ := product'.countable_absorb_l hZFC (V := M) hw' fa' empty' alphabet' hκ space bound O order s onto small
  obtain ⟨b,hb⟩ := g.inhabited
  obtain ⟨j,checks,_,_⟩ := check_map_l (product'.order_l hZF) hZF g hb
  have ground a := (gval_check_map_l (product'.order_l hZF) hZF g hb j checks a (j a)).mpr rfl
  have names := (Smem_d.product_real_names_l hZF source trans rank native hw fa product g j ground).2
  exact ⟨G,g,ι,ii,ifull,over,j,ground,fun ν base x real =>
    ⟨capture ν base x real,names (ι x) (capture ν base x real)⟩⟩

end YesMetaZFC.Model.Forcing.Internal
