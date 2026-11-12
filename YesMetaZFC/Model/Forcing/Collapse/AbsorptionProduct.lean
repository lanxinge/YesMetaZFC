import YesMetaZFC.Model.Forcing.Proper.Hereditary.Cardinal
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable
import YesMetaZFC.Model.Forcing.Collapse.KripkeMap
import YesMetaZFC.Model.Forcing.Collapse.PartialFunctionCertificate
import YesMetaZFC.Model.Forcing.Boolean.DenseCompletion
import YesMetaZFC.Model.Forcing.Boolean.QuotientBasisDense
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Boolean.NameQuotient
import YesMetaZFC.Model.Forcing.Boolean.QuotientBasisMap
import YesMetaZFC.Model.Forcing.Boolean.DenseRange
import YesMetaZFC.Model.Forcing.Collapse.FiniteSequenceCertificate
import YesMetaZFC.Model.Forcing.Boolean.ExtensionRealization
import YesMetaZFC.Model.Forcing.TwoStep.ProductExtension
import YesMetaZFC.Model.Forcing.Ground.TreeShift

/-! # 小有限序列力迫保持其上的不可数基数

若 α<κ 且 κ 不可数，先在 κ 内取控制 α 和 ω 的无限基数 ν。
全部内部有限 α 列可单射到 ν；小力迫基数保持定理遂应用于同一个检查名字嵌入。
这里不要求 κ 正则或不可达，也不要求 α 本身是无限基数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_uncountable_l {Q T w ω α κ c : M.Domain} (O : Cond_order_d M Q T w)
    (hω : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (hα : M.mem α κ)
    (space : Fseq_space_d I ω α Q) {H : M.Domain → Prop} (generic : Generic_d M Q T w H) (hc : H c)
    (j : M.Domain → (extension_l M hZF Q T w H).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF Q T w H).mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    (checks : ∀ a t, Check_d M c a t → Qval_d M Q T w H t (j a)) :
    let E := extension_l M hZF Q T w H
    let J := kpair_interpretation_l E (extension_ext_l O hZF generic) (internal_pair_l O hZF generic)
    ∃ ν, M.mem ν κ ∧ M.IsInfiniteCardinal I ω ν ∧ M.CardinalLessOrEqual I Q ν ∧
      E.IsUncountableCardinal J (j ω) (j κ) := by
  obtain ⟨ν,hν,inf,bound,_⟩ := ZF.common_cardinal_l I hZF hκ.1.1 hκ.2 hα hα
  have size := ZF.fseq_bound_l I hZF hω inf bound space
  have cardinal := small_cardinal_l O hZFC generic hω hκ.2 hν size hc j inj full checks hκ.1
  exact ⟨ν,hν,inf,size,cardinal,(image_member_l j inj full).mpr hκ.2⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## Kripke／Solovay 的可数坍缩刻画

若条件域大小不超过不可数基数 κ，且 a 迫使旧 κ 可数，则原正锥 B↾a 与
Col(ω,κ) 的模型内部正则开完备化之间存在实际双射完全同态。
既不要求 κ 正则，也不要求地模型外部可数或良基。
标准刻画见 Jech《Set Theory》Lemma 26.7；Kripke 吸收结论见紧接的 Theorem 26.8。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem kripke_l {B R z a ω κ : M.Domain} (O : Cond_order_d M B R z)
    (hω : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (size : M.CardinalLessOrEqual I B κ)
    (ha : M.mem a B) (hz : a ≠ z) (collapse : Collapses_d B R z a ω κ) : ∃ C F S A T e D V d G,
      (∀ p, M.mem p C ↔ Below_d M B R z p a) ∧ Fseq_space_d I ω κ F ∧
      (∀ s t, Entry_d M s t S ↔ M.mem s F ∧ M.mem t F ∧ M.MemberSubset t s) ∧
      (∀ U, M.mem U A ↔ Ropen_d F S F U) ∧
      (∀ U W, Entry_d M U W T ↔ M.mem U A ∧ M.mem W A ∧ M.MemberSubset U W) ∧ BooleanZF.Cba_d I A T e ∧
      (∀ U, M.mem U D ↔ Ropen_d C R z U) ∧
      (∀ U W, Entry_d M U W V ↔ M.mem U D ∧ M.mem W D ∧ M.MemberSubset U W) ∧ BooleanZF.Cba_d I D V d ∧
      M.IsSetBijectionFromTo I G D A ∧ BooleanZF.Cbh_d I D V d A T e G := by
  obtain ⟨b,T₀,w,f,hb,ab,hT,hw,name⟩ := collapse.name_l hZFC O ha hz
  obtain ⟨C,F,S,Γ,cone,target,space,order,source,map⟩ := kripke_map_l hZFC O hω hκ size name hb ab hT hw
  obtain ⟨A,T,e,D,V,d,G,fa,oa,ca,fd,od,cd,bij,complete,_⟩ := map.completion_l hZF source target
  exact ⟨C,F,S,A,T,e,D,V,d,G,cone,space,order,fa,oa,ca,fd,od,cd,bij,complete⟩

private theorem ropen_positive_l {B R z C U : M.Domain}
    (carrier : ∀ p, M.mem p C ↔ M.mem p B ∧ p ≠ z) : Ropen_d C R z U ↔ Ropen_d B R z U := by
  have below p q : Below_d M C R z p q ↔ Below_d M B R z p q :=
    ⟨fun h => ⟨((carrier p).mp h.1).1,h.2⟩,fun h => ⟨(carrier p).mpr ⟨h.1,h.2.1⟩,h.2⟩⟩
  constructor
  · rintro ⟨bound,lower,closed⟩
    refine ⟨fun p hp => (carrier p).mp (bound p hp).1,?_,?_⟩
    · intro p q _ hq hp
      exact lower p q (bound p hp).1 ((below q p).mpr hq) hp
    · intro p hp hz dense
      apply closed p ((carrier p).mpr ⟨hp,hz⟩) hz
      intro q hq
      obtain ⟨r,hr,hu⟩ := dense q ((below q p).mp hq)
      exact ⟨r,(below r q).mpr hr,hu⟩
  · rintro ⟨bound,lower,closed⟩
    refine ⟨fun p hp => ⟨(carrier p).mpr (bound p hp),(bound p hp).2⟩,?_,?_⟩
    · intro p q hp hq hu
      exact lower p q ((carrier p).mp hp).1 ((below q p).mp hq) hu
    · intro p hp hz dense
      apply closed p ((carrier p).mp hp).1 hz
      intro q hq
      obtain ⟨r,hr,hu⟩ := dense q ((below q p).mpr hq)
      exact ⟨r,(below r q).mp hr,hu⟩

/-- 有最大正条件时，直接得到整个原偏序的完备化同构。 -/
theorem kripke_top_l {B R z a ω κ : M.Domain} (O : Cond_order_d M B R z)
    (hω : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (size : M.CardinalLessOrEqual I B κ)
    (ha : M.mem a B) (hz : a ≠ z) (top : ∀ q, M.mem q B → q ≠ z → Entry_d M q a R)
    (collapse : Collapses_d B R z a ω κ) : ∃ F S A T e D V d G,
      Fseq_space_d I ω κ F ∧
      (∀ s t, Entry_d M s t S ↔ M.mem s F ∧ M.mem t F ∧ M.MemberSubset t s) ∧
      (∀ U, M.mem U A ↔ Ropen_d F S F U) ∧
      (∀ U W, Entry_d M U W T ↔ M.mem U A ∧ M.mem W A ∧ M.MemberSubset U W) ∧ BooleanZF.Cba_d I A T e ∧
      (∀ U, M.mem U D ↔ Ropen_d B R z U) ∧
      (∀ U W, Entry_d M U W V ↔ M.mem U D ∧ M.mem W D ∧ M.MemberSubset U W) ∧ BooleanZF.Cba_d I D V d ∧
      M.IsSetBijectionFromTo I G D A ∧ BooleanZF.Cbh_d I D V d A T e G := by
  obtain ⟨C,F,S,A,T,e,D,V,d,G,cone,space,order,fa,oa,ca,fd,od,cd,bij,complete⟩ := kripke_l hZFC O hω hκ size ha hz collapse
  have carrier p : M.mem p C ↔ M.mem p B ∧ p ≠ z :=
    (cone p).trans ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,top p h.1 h.2⟩⟩
  exact ⟨F,S,A,T,e,D,V,d,G,space,order,fa,oa,ca,fun U => (fd U).trans (ropen_positive_l carrier),od,cd,bij,complete⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 商的旧部分函数条件迫使原目标集合可数

逐坐标和逐值的旧稠密集在商上仍稠密。商的旧条件保持原部分函数图，
其泛型并图因此给出实际满射；每个商条件均取得通常的存在式坍缩证书。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
variable {j : M.Domain → N.Domain} (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
variable {P R z C Γ X Y : M.Domain} {D B S F : N.Domain}
include hM hN inj full

theorem Qb_d.psurj_l (k : Qb_d j C R Γ D B S F) (O : Cond_order_d M P R z)
    (cone : Ropen_d P R z C) (graph : ∀ p A, Entry_d M p A Γ → Rpr_d P R z p A)
    (trace : Qtrace_d j P R z Γ D) (source : Psurj_d hM P R z X Y) : Psurj_d hN B S B (j X) (j Y) := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have refl p (hp : N.mem p B) : Below_d N B S B p p := by
    obtain ⟨q,hq,rfl,_⟩ := (k.carrier p).mp hp
    exact ⟨hp,fun eq => KP.mem_irrefl_d (ZF.modelsKP hN) B (eq ▸ hp),
      (k.order (j q) (j q)).mpr ⟨hp,hp,(entry q q R).mp (O.refl q (cone.1 q hq).1)⟩⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl,_⟩ := (k.carrier p).mp hp
    exact image_pfn_l (hN := hN.1) (pairN := KP.exists_pair (ZF.modelsKP hN)) j inj full
      (source.function q (cone.1 q hq).1)
  · intro p q pq
    obtain ⟨hp,hq,pq⟩ := (k.order p q).mp pq
    obtain ⟨a,_,rfl,_⟩ := (k.carrier p).mp hp
    obtain ⟨b,_,rfl,_⟩ := (k.carrier q).mp hq
    intro x hx
    obtain ⟨v,hv,rfl⟩ := (full b x).mp hx
    exact (image_member_l j inj full).mpr (source.order a b ((entry a b R).mpr pq) v hv)
  · intro x hx p hp _
    obtain ⟨a,ha,rfl⟩ := (full X x).mp hx
    let ρ : Env M 1 := ⟨fun _ => a,fun _ => a⟩
    let φ : UnarySchema 1 := { body := .existsE (entry_m (.bound 2) .newest (.bound 1)) }
    obtain ⟨E,members⟩ := ZF.separation_exists_d hM φ ρ C
    have read q : M.mem q E ↔ M.mem q C ∧ ∃ b, Entry_d M a b q := by
      apply (members q).trans (and_congr_right fun _ => ?_)
      simp only [φ,Formula.satisfies_exists_iff,entry_sat_l M hM.1]; rfl
    have dense q (hq : M.mem q C) : ∃ r, Below_d M P R z r q ∧ M.mem r E := by
      obtain ⟨r,hr,b,ab⟩ := source.input a ha q (cone.1 q hq).1 (cone.1 q hq).2
      exact ⟨r,hr,(read r).mpr ⟨cone.2.1 q r (cone.1 q hq).1 hr hq,b,ab⟩⟩
    obtain ⟨q,hq,qE⟩ := k.dense_set_l hM hN inj full O cone graph trace dense p hp p (refl p hp)
    obtain ⟨r,hr,rfl⟩ := (full E q).mp qE
    obtain ⟨_,b,ab⟩ := (read r).mp hr
    exact ⟨j r,hq,j b,(entry a b r).mp ab⟩
  · intro y hy p hp _
    obtain ⟨a,ha,rfl⟩ := (full Y y).mp hy
    let ρ : Env M 1 := ⟨fun _ => a,fun _ => a⟩
    let φ : UnarySchema 1 := { body := .existsE (entry_m .newest (.bound 2) (.bound 1)) }
    obtain ⟨E,members⟩ := ZF.separation_exists_d hM φ ρ C
    have read q : M.mem q E ↔ M.mem q C ∧ ∃ b, Entry_d M b a q := by
      apply (members q).trans (and_congr_right fun _ => ?_)
      simp only [φ,Formula.satisfies_exists_iff,entry_sat_l M hM.1]; rfl
    have dense q (hq : M.mem q C) : ∃ r, Below_d M P R z r q ∧ M.mem r E := by
      obtain ⟨r,hr,b,ba⟩ := source.output a ha q (cone.1 q hq).1 (cone.1 q hq).2
      exact ⟨r,hr,(read r).mpr ⟨cone.2.1 q r (cone.1 q hq).1 hr hq,b,ba⟩⟩
    obtain ⟨q,hq,qE⟩ := k.dense_set_l hM hN inj full O cone graph trace dense p hp p (refl p hp)
    obtain ⟨r,hr,rfl⟩ := (full E q).mp qE
    obtain ⟨_,b,ba⟩ := (read r).mp hr
    exact ⟨j r,hq,j b,(entry b a r).mp ba⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 有限序列坍缩的实际小商及坍缩证书

对原名字读取的同一个 H，在 M[H] 中构造旧有限序列商，其大小不超过 j(κ)。
每个条件迫使 j(κ) 为 j(ω) 的满射像；旧主正则开图是到原商的稠密映射，
并将原大扩张识别为这一小商泛型之上的二步扩张。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Nh_d.fseq_quotient_l {B R b p Q T w 𝒟 τ K S e C L V d F ω κ : M.Domain}
    (h : Nh_d hZF B R B b p Q T w 𝒟 τ K S e C L V d F)
    (hω : M.IsOmega ω) (hκ : M.IsInfiniteCardinal I ω κ) (space : Fseq_space_d I ω κ B)
    (order : ∀ q r, Entry_d M q r R ↔ M.mem q B ∧ M.mem r B ∧ M.MemberSubset r q)
    {G : M.Domain → Prop} (generic : Generic_d M B R B G) (hp : G p) :
    ∃ H : M.Domain → Prop, ∃ small : Generic_d M Q T w H,
      (∀ q, H q ↔ ∃ a, Check_d M b q a ∧ ∃ r, G r ∧ Mem_force_d M B R B r a τ) ∧
      let E := extension_l M hZF Q T w H
      let hE := preserves_zf_l h.small hZF small
      ∃ c, H c ∧ ∃ j : M.Domain → E.Domain, Function.Injective j ∧
        (∀ a y, E.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y) ∧
        (∀ a t, Check_d M c a t → Qval_d M Q T w H t (j a)) ∧ E.IsOmega (j ω) ∧
        ∃ Γ, M.IsSetFunctionFromTo I Γ C L ∧ ∃ D W P U Φ : E.Domain,
          Qb_d j C R Γ D P U Φ ∧ Cond_order_d E P U P ∧ Cond_order_d E D W D ∧
          Dmap_d P U P D W D Φ ∧
          E.CardinalLessOrEqual (kpair_interpretation_l E hE.1 (KP.exists_pair (ZF.modelsKP hE))) P (j κ) ∧
          (∃ A, E.MemberSubset A D ∧
            E.CardinalLessOrEqual (kpair_interpretation_l E hE.1 (KP.exists_pair (ZF.modelsKP hE))) A (j κ) ∧
            ∀ q, E.mem q D → ∃ r, E.mem r A ∧ Below_d E D W D r q) ∧
          (∀ q, E.mem q P → Collapses_d P U P q (j ω) (j κ)) ∧
          let G' := Qgeneric_d j (fun X => M.mem X L ∧ ∃ q, G q ∧ M.mem q X)
          Generic_d E D W D G' ∧ Generic_d E P U P (Pull_generic_d E Φ G') ∧
          Miso_over_d (extension_l M hZF B R B G) (extension_l E hE P U P (Pull_generic_d E Φ G'))
            (Gval_d M B R B G) (fun x => Gval_d E P U P (Pull_generic_d E Φ G') (j x)) := by
  obtain ⟨zero,_,hzero⟩ := hω.1.1
  obtain ⟨f,hf⟩ := hκ.2
  obtain ⟨x,hx,_⟩ := hf.1.2.2 zero hzero
  have source := fseq_psurj_l hZF hω space order ⟨x,hx⟩
  obtain ⟨id,identity⟩ := ZF.exists_identityBijection hZF I κ
  have size := ZF.fseq_bound_l I hZF hω hκ ⟨id,identity.1⟩ space
  obtain ⟨H,small,original,A,J,_,_,_,_,_,_,P,_,_,c,hc,j,ji,full,checks,D,quotient,_,_,_,Γ,basis,graph,trace,
      ξ,ν,_,_,_,b',W,C',S',J',_,_,_,edges,OJ,genericJ,_,_,f,_,_,_,_,iso⟩ := h.quotient_l hZF generic hp
  let E := extension_l M hZF Q T w H
  have hE : E.Models ZF := preserves_zf_l h.small hZF small
  have omega : E.IsOmega (j ω) := image_omega_l (hEN := hE.1) j ji full hZF
    (internal_foundation_l h.small hZF small) hω (fun X => KP.difference_exists_d (ZF.modelsKP hE) X (j ω))
  have OC : Cond_order_d M C R B := {
    refl := fun q hq => h.big.refl q (h.cone.1 q hq).1
    trans := fun q r s hq hr hs => h.big.trans q r s (h.cone.1 q hq).1 (h.cone.1 r hr).1 (h.cone.1 s hs).1
    zero := fun q hq => h.big.zero q (h.cone.1 q hq).1 }
  obtain ⟨Bq,Sq,Φ,k,OB,fn⟩ := quotient_basis_l hZF hE j ji full OC basis D
  have old X (hX : E.mem X D) : ∃ Y, M.mem Y L ∧ j Y = X := by
    obtain ⟨Y,hY,_,eq,_⟩ := (quotient X).mp hX
    exact ⟨Y,hY,eq⟩
  have map := k.map_l hZF hE ji full h.big h.cone h.localFamily h.localOrder basis graph old edges fn trace
  have bound := k.size_l hZF hE ji full (fun q hq => (h.cone.1 q hq).1) size
  have ordinal : E.IsOrdinal (j κ) := image_ordinal_l j ji full hZF.1 (internal_foundation_l h.small hZF small) hκ.1.1
  obtain ⟨Aq,_,subAq,sizeAq,denseAq⟩ := map.small_range_l hE fn ordinal bound
  have certificate := k.psurj_l hZF hE ji full h.big h.cone graph trace source
  obtain ⟨a,ha⟩ := genericJ.inhabited
  have regular := map.regular_l OJ
  have inhabited := regular.dense_hit_l hE OJ genericJ ha (fun q hq => map.dense q hq.1 hq.2.1)
  have smallGeneric := reg_generic_l OB OJ hE regular genericJ inhabited
  have smallIso := (map.ground_l hE OB OJ genericJ).comp_l j
  exact ⟨H,small,original,c,hc,j,ji,full,checks,omega,Γ,basis,D,J',Bq,Sq,Φ,k,OB,OJ,map,bound,
    ⟨Aq,subAq,sizeAq,fun q hq => denseAq q hq (fun eq => KP.mem_irrefl_d (ZF.modelsKP hE) D (eq ▸ hq))⟩,
    (fun q hq => certificate.collapse_l hE OB hq (fun eq => KP.mem_irrefl_d (ZF.modelsKP hE) Bq (eq ▸ hq))),
    genericJ,smallGeneric,iso.trans_l smallIso.symm_l⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 小有限序列泛型的坍缩吸收同构

同一个原名字读出 H；小条件域的实际大小界保持 j(κ) 为不可数基数。
对已经构造的小商应用 Kripke 稠密图，在原商泛型接受的正锥下回拉，
得到 M[H] 上的 Col(ω,j(κ)) 泛型及原大扩张与其扩张的地模型参数保持同构。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem Nh_d.fseq_absorption_l {B R b p Q T w 𝒟 τ K S e C L V d F ω α κ : M.Domain}
    (h : Nh_d hZF B R B b p Q T w 𝒟 τ K S e C L V d F)
    (hω : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (hα : M.mem α κ)
    (space : Fseq_space_d I ω κ B)
    (order : ∀ q r, Entry_d M q r R ↔ M.mem q B ∧ M.mem r B ∧ M.MemberSubset r q)
    (smallSpace : Fseq_space_d I ω α Q)
    {G : M.Domain → Prop} (generic : Generic_d M B R B G) (hp : G p) :
    ∃ H : M.Domain → Prop, ∃ small : Generic_d M Q T w H,
      (∀ q, H q ↔ ∃ a, Check_d M b q a ∧ ∃ r, G r ∧ Mem_force_d M B R B r a τ) ∧
      let E := extension_l M hZF Q T w H
      let hE := ZFC.models_zf_l (preserves_zfc_l h.small hZFC small)
      let J := kpair_interpretation_l E hE.1 (KP.exists_pair (ZF.modelsKP hE))
      ∃ c, H c ∧ ∃ j : M.Domain → E.Domain, Function.Injective j ∧
        (∀ a y, E.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y) ∧
        (∀ a t, Check_d M c a t → Qval_d M Q T w H t (j a)) ∧
        E.IsOmega (j ω) ∧ E.IsUncountableCardinal J (j ω) (j κ) ∧
        ∃ ν, M.mem ν κ ∧ M.IsInfiniteCardinal I ω ν ∧ M.CardinalLessOrEqual I Q ν ∧
        ∃ P U : E.Domain, ∃ G' : E.Domain → Prop,
          Fseq_space_d J (j ω) (j κ) P ∧
          (∀ s t, Entry_d E s t U ↔ E.mem s P ∧ E.mem t P ∧ E.MemberSubset t s) ∧
          Cond_order_d E P U P ∧ Generic_d E P U P G' ∧
          Miso_over_d (extension_l M hZF B R B G) (extension_l E hE P U P G')
            (Gval_d M B R B G) (fun x => Gval_d E P U P G' (j x)) ∧
          let N := extension_l M hZF B R B G
          ∃ i : E.Domain → N.Domain, Function.Injective i ∧
            (∀ a y, N.mem y (i a) ↔ ∃ c, E.mem c a ∧ i c = y) ∧
            (∀ x y, Gval_d M B R B G x y ↔ i (j x) = y) ∧
            ∃ 𝒟, E.IsPowerSetOf 𝒟 P ∧ ∃ g : N.Domain,
              (∀ y, N.mem y g ↔ ∃ p, G' p ∧ i p = y) ∧
              Gset_d (i P) (i U) (i P) (i 𝒟) g ∧
              ∃ f : (extension_l E hE P U P G').Domain → N.Domain,
                (∀ a b, a ∈ b ↔ N.mem (f a) (f b)) ∧ Function.Injective f ∧ Function.Surjective f ∧
                (∀ x a, Gval_d E P U P G' x a ↔ i x = f a) ∧
                ∀ y, ∃ t a, Name_d E P t ∧ Qval_d E P U P G' t a ∧ f a = y := by
  have infinite : M.IsInfiniteCardinal I ω κ :=
    ⟨hκ.1,ZF.exists_inclusionInjection hZF I (hκ.1.1.transitive ω hκ.2)⟩
  obtain ⟨H,small,original,c,hc,j,inj,full,checks,omega,Γ,_,D,W,P,U,Φ,_,OP,_,_,size,_,collapse,_,gP,iso⟩ :=
    h.fseq_quotient_l hZF hω infinite space order generic hp
  let E := extension_l M hZF Q T w H
  have hE : E.Models ZFC := preserves_zfc_l h.small hZFC small
  let hEZF := ZFC.models_zf_l hE
  -- 保持结论使用商分解返回的同一个 j 及其检查名字对应。
  obtain ⟨ν,hν,hνInf,bound,uncountable⟩ := fseq_uncountable_l hZFC h.small hω hκ hα smallSpace small hc j inj full checks
  obtain ⟨a,ha⟩ := gP.inhabited
  have pos := gP.proper a ha
  -- 坍缩名字、正锥、κ 叉稠密树均由已有构造实际取得。
  obtain ⟨b₀,T₀,w₀,f₀,hb₀,ab₀,hT₀,hw₀,name⟩ := (collapse a pos.1).name_l hE OP pos.1 pos.2
  obtain ⟨C₀,F₀,S₀,Δ,cone,_,sequences,sequenceOrder,OF,map⟩ :=
    kripke_map_l hE OP omega uncountable size name hb₀ ab₀ hT₀ hw₀
  have localMap := map.cone_regular_l OP pos.1 cone
  have dense q (hq : Below_d E P U P q a) : ∃ s t, Entry_d E s t Δ ∧ Entry_d E t q U :=
    map.dense q ((cone q).mpr hq) hq.2.1
  -- 沿实际稠密图回拉商泛型；往返名字给出扩张同构的满射性。
  have hit := localMap.dense_hit_l hEZF OP gP ha dense
  have collapseGeneric := reg_generic_l OF OP hEZF localMap gP hit
  let G' := Pull_generic_d E Δ (Pull_generic_d E Φ (Qgeneric_d j (fun X => M.mem X L ∧ ∃ q, G q ∧ M.mem q X)))
  have comparison := (localMap.dense_ground_l hEZF OF OP map.functional gP ha dense).comp_l j
  have absorption := iso.trans_l comparison.symm_l
  exact ⟨H,small,original,c,hc,j,inj,full,checks,omega,uncountable,ν,hν,hνInf,bound,
    F₀,S₀,G',sequences,sequenceOrder,OF,collapseGeneric,absorption,
    absorption.realize_l hEZF OF collapseGeneric (extension_ext_l h.big hZF generic)⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 给定小泛型集合的实际吸收

从原大扩张中的小泛型集合取得原名字，自动构造完全同态、主核和商。
读回的小泛型与给定集合逐条件相等；所有扩张和名字代表均沿同一次识别取得。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_absorption_value_l {B R Q T w ω α κ b : M.Domain}
    (O : Cond_order_d M B R B) (L : Cond_order_d M Q T w)
    (hω : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (hα : M.mem α κ)
    (space : Fseq_space_d I ω κ B)
    (order : ∀ q r, Entry_d M q r R ↔ M.mem q B ∧ M.mem r B ∧ M.MemberSubset r q)
    (smallSpace : Fseq_space_d I ω α Q) {G : M.Domain → Prop}
    (generic : Generic_d M B R B G) (hb : G b)
    (k : M.Domain → (extension_l M hZF B R B G).Domain) (ki : Function.Injective k)
    (full : ∀ a y, (extension_l M hZF B R B G).mem y (k a) ↔ ∃ x, M.mem x a ∧ k x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M B R B G t (k a))
    (Y : (extension_l M hZF B R B G).Domain)
    (small : Generic_d M Q T w (fun q => (extension_l M hZF B R B G).mem (k q) Y))
    (bound : (extension_l M hZF B R B G).MemberSubset Y (k Q)) :
    let H := fun q => (extension_l M hZF B R B G).mem (k q) Y
    let E := extension_l M hZF Q T w H
    let hE := ZFC.models_zf_l (preserves_zfc_l L hZFC small)
    let J := kpair_interpretation_l E hE.1 (KP.exists_pair (ZF.modelsKP hE))
    let N := extension_l M hZF B R B G
    ∃ c, H c ∧ ∃ j : M.Domain → E.Domain, Function.Injective j ∧
      (∀ a y, E.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y) ∧
      (∀ a t, Check_d M c a t → Qval_d M Q T w H t (j a)) ∧
      E.IsOmega (j ω) ∧ E.IsUncountableCardinal J (j ω) (j κ) ∧
      ∃ P U : E.Domain, ∃ G' : E.Domain → Prop,
        Fseq_space_d J (j ω) (j κ) P ∧
        (∀ s t, Entry_d E s t U ↔ E.mem s P ∧ E.mem t P ∧ E.MemberSubset t s) ∧
        Cond_order_d E P U P ∧ Generic_d E P U P G' ∧
        ∃ i : E.Domain → N.Domain, Function.Injective i ∧
          (∀ a y, N.mem y (i a) ↔ ∃ c, E.mem c a ∧ i c = y) ∧ (∀ x, i (j x) = k x) ∧
          ∃ 𝒟, E.IsPowerSetOf 𝒟 P ∧ ∃ g : N.Domain,
            (∀ y, N.mem y g ↔ ∃ p, G' p ∧ i p = y) ∧ Gset_d (i P) (i U) (i P) (i 𝒟) g ∧
            ∃ f : (extension_l E hE P U P G').Domain → N.Domain,
              (∀ a b, a ∈ b ↔ N.mem (f a) (f b)) ∧ Function.Injective f ∧ Function.Surjective f ∧
              (∀ x a, Gval_d E P U P G' x a ↔ i x = f a) ∧
              ∀ y, ∃ t a, Name_d E P t ∧ Qval_d E P U P G' t a ∧ f a = y := by
  obtain ⟨τ,_,value⟩ := value_name_l Y
  obtain ⟨p,𝒟,K,S,e,C,A,V,d,F,hp,data,_⟩ :=
    gn_value_complete_l hZF O L generic hb value k ki full checks small bound
  obtain ⟨H,hH,read,c,hc,j,ji,jfull,jcheck,omega,card,ν,_,_,_,P,U,G',fs,ord,OP,gP,_,realize⟩ :=
    data.fseq_absorption_l hZFC hω hκ hα space order smallSpace generic hp
  have same : H = fun q => (extension_l M hZF B R B G).mem (k q) Y := by
    funext q
    apply propext
    apply (read q).trans
    constructor
    · rintro ⟨a,qa,force⟩
      exact (qval_mem_forcing_l O hZF generic (checks q a qa) value).mp force
    · intro hq
      obtain ⟨a,qa,_,_⟩ := zf_check_l M hZF (generic.proper b hb).1 q
      exact ⟨a,qa,(qval_mem_forcing_l O hZF generic (checks q a qa) value).mpr hq⟩
  subst H
  obtain ⟨i,ii,ifull,fixed,D,power,g,filter,gset,f,mem,fi,onto,ground,names⟩ := realize
  refine ⟨c,hc,j,ji,jfull,jcheck,omega,card,P,U,G',fs,ord,OP,gP,
    i,ii,ifull,?_,D,power,g,filter,gset,f,mem,fi,onto,ground,names⟩
  intro x
  exact (fixed x (k x)).mp ((gval_check_map_l O hZF generic hb k checks x (k x)).mpr rfl)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 将实际吸收接回原坍缩积

中间模型中的有限列条件域就是旧大条件域的规范像；关系只需在条件域上相同。
因此原小泛型集合和吸收得到的大泛型集合，确实给出原积的泛型及地参数保持同构。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_product_absorption_l {Q T P U C R b₀ b ω α κ : M.Domain}
    (O : Cond_order_d M Q T Q) (L : Cond_order_d M P U P) (OP : Cond_order_d M C R C)
    (product : Prod_d hZF Q T P U C R) (hb₀ : M.mem b₀ Q) (top : ∀ q, M.mem q Q → Entry_d M q b₀ T)
    (hw : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (hα : M.mem α κ)
    (space : Fseq_space_d I ω κ P)
    (order : ∀ p q, Entry_d M p q U ↔ M.mem p P ∧ M.mem q P ∧ M.MemberSubset q p)
    (smallSpace : Fseq_space_d I ω α Q)
    {G : M.Domain → Prop} (generic : Generic_d M P U P G) (hb : G b)
    (k : M.Domain → (extension_l M hZF P U P G).Domain) (ki : Function.Injective k)
    (full : ∀ a y, (extension_l M hZF P U P G).mem y (k a) ↔ ∃ x, M.mem x a ∧ k x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M P U P G t (k a))
    (H : (extension_l M hZF P U P G).Domain)
    (small : Generic_d M Q T Q (fun q => (extension_l M hZF P U P G).mem (k q) H))
    (bound : (extension_l M hZF P U P G).MemberSubset H (k Q)) :
    let N := extension_l M hZF P U P G
    let H₀ := fun q => N.mem (k q) H
    let E := extension_l M hZF Q T Q H₀
    ∃ j : M.Domain → E.Domain, Function.Injective j ∧
      (∀ a y, E.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y) ∧
      (∀ a t, Check_d M b₀ a t → Qval_d M Q T Q H₀ t (j a)) ∧
      ∃ J : E.Domain, ∃ G' : E.Domain → Prop,
        Cond_order_d E (j P) J (j P) ∧ Generic_d E (j P) J (j P) G' ∧
        (∀ x y, E.mem x (j P) → E.mem y (j P) → (Entry_d E x y (j U) ↔ Entry_d E x y J)) ∧
        ∃ i : E.Domain → N.Domain, Function.Injective i ∧
          (∀ a y, N.mem y (i a) ↔ ∃ x, E.mem x a ∧ i x = y) ∧ (∀ x, i (j x) = k x) ∧
          ∃ g : N.Domain, (∀ y, N.mem y g ↔ ∃ p, G' p ∧ i p = y) ∧
            (∀ p, N.mem (k p) g ↔ G' (j p)) ∧ N.MemberSubset g (k P) ∧
            Generic_d M C R C (Prod_generic_d hZF C j G') ∧
            (∀ v, Prod_generic_d hZF C j G' v ↔ M.mem v C ∧
              ∃ q p, KPair_d M v q p ∧ N.mem (k q) H ∧ N.mem (k p) g) ∧
            Miso_over_d (extension_l M hZF C R C (Prod_generic_d hZF C j G')) N
              (Gval_d M C R C (Prod_generic_d hZF C j G')) (fun x y => k x = y) := by
  obtain ⟨c,hc,j,ji,jfull,jchecks,omega,_,P',J,G',fs,ord,OJ,generic',i,ii,ifull,fixed,
      𝒟,_,g,filter,_,f,mem,fi,onto,ground,_⟩ :=
    fseq_absorption_value_l hZFC L O hw hκ hα space order smallSpace generic hb k ki full checks H small bound
  let N := extension_l M hZF P U P G
  let H₀ := fun q => N.mem (k q) H
  let E := extension_l M hZF Q T Q H₀
  have hE : E.Models ZF := preserves_zf_l O hZF small
  have old := image_fseq_l hZF hE j ji jfull hw omega space
  have same : P' = j P := hE.1.eq_of_same_members P' (j P) (fun s => (fs s).trans (old s).symm)
  subst P'
  have comparison : ∀ x y, E.mem x (j P) → E.mem y (j P) →
      (Entry_d E x y (j U) ↔ Entry_d E x y J) := by
    intro x y hx hy
    obtain ⟨a,ha,rfl⟩ := (jfull P x).mp hx
    obtain ⟨b,hb,rfl⟩ := (jfull P y).mp hy
    have entry := image_entry_iff_l j ji jfull (KP.exists_pair (ZF.modelsKP hZF)) hE.1 a b U
    constructor
    · intro ab
      exact (ord (j a) (j b)).mpr ⟨(image_member_l j ji jfull).mpr ha,(image_member_l j ji jfull).mpr hb,
        (image_subset_iff_l j ji jfull).mpr ((order a b).mp (entry.mpr ab)).2.2⟩
    · intro ab
      exact entry.mp ((order a b).mpr ⟨ha,hb,
        (image_subset_iff_l j ji jfull).mp ((ord (j a) (j b)).mp ab).2.2⟩)
  have accepted : H₀ b₀ := small.upward c b₀ hc hb₀ (top c (small.proper c hc).1)
  have canonical := check_map_change_l O hZF small hc accepted j jchecks
  obtain ⟨prodGeneric,prodIso⟩ := product.extension_l hZF O L OP top small accepted j canonical comparison OJ generic'
  have last : Miso_over_d (extension_l E hE (j P) J (j P) G') N
      (fun x => Gval_d E (j P) J (j P) G' (j x)) (fun x y => k x = y) := by
    refine ⟨f,mem,fi,onto,fun x a => ?_⟩
    exact (ground (j x) a).trans (by rw [fixed x])
  have acceptedBig p : N.mem (k p) g ↔ G' (j p) := by
    apply (filter (k p)).trans
    exact ⟨fun ⟨r,hr,eq⟩ => ii (eq.trans (fixed p).symm) ▸ hr,fun hp => ⟨j p,hp,fixed p⟩⟩
  refine ⟨j,ji,jfull,canonical,J,G',OJ,generic',comparison,i,ii,ifull,fixed,g,filter,acceptedBig,?_,
    prodGeneric,?_,prodIso.trans_l last⟩
  · intro y hy
    obtain ⟨r,hr,rfl⟩ := (filter y).mp hy
    exact fixed P ▸ (ifull (j P) (i r)).mpr ⟨r,(generic'.proper r hr).1,rfl⟩
  · intro v
    change (M.mem v C ∧ ∃ q p, KPair_d M v q p ∧ H₀ q ∧ G' (j p)) ↔ _
    exact and_congr_right fun _ => exists_congr fun q => exists_congr fun p =>
      and_congr_right fun _ => and_congr_right fun _ => (acceptedBig p).symm

end YesMetaZFC.Model.Forcing.Internal
