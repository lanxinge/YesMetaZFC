import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Automorphism.RealSetName
import YesMetaZFC.Model.Forcing.Embedding.Rank
import YesMetaZFC.Model.SetTheory.Internal.RealTrace

/-! # 地模型自同构及其滤子回拉在扩张中的同一解释

先在地模型构造条件自同构，再搬到成员满扩张。
回拉滤子的规范像等于规范像滤子的回拉，因而有限改写可以保留地模型中的实际图。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem image_aut_l (hM : M.Models KP) (hN : N.Models KP)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {B R z F : M.Domain} (h : Aut_d M B R z F) : Aut_d N (e B) (e R) (e z) (e F) := by
  have bij := aut_bij_l hM.1 (KP.exists_pair hM) h
  have fn := image_injection_l (hEN := hN.1) (hPN := KP.exists_pair hN) e inj full bij.1
  have entry := image_entry_iff_l e inj full (KP.exists_pair hM) hN.1
  refine aut_of_bij_l hN.1 (KP.exists_pair hN) ⟨fn,?_⟩ ?_ ?_
  · intro q hq
    obtain ⟨b,hb,rfl⟩ := (full B q).mp hq
    obtain ⟨a,ha,ab⟩ := bij.2 b hb
    exact ⟨e a,(image_member_l e inj full).mpr ha,(entry a b F).mp ab⟩
  · intro p q s t ps qt
    obtain ⟨a,b,ab,rfl,rfl⟩ := (image_entries_l e full h.graph p s).mp ps
    obtain ⟨c,d,cd,rfl,rfl⟩ := (image_entries_l e full h.graph q t).mp qt
    exact (entry a c R).symm.trans ((h.order a c b d ab cd).trans (entry b d R))
  · intro p q pq
    obtain ⟨a,b,ab,rfl,rfl⟩ := (image_entries_l e full h.graph p q).mp pq
    exact ⟨fun eq => congrArg e ((h.zero a b ab).mp (inj eq)),
      fun eq => congrArg e ((h.zero a b ab).mpr (inj eq))⟩

/-- 这个等式同时识别两个实际泛型谓词，不另外选择滤子。 -/
theorem image_pull_l (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {B R z F : M.Domain} (h : Aut_d M B R z F) (G : M.Domain → Prop) :
    Pull_generic_d N (e F) (Em_generic_d e G) = Em_generic_d e (Pull_generic_d M F G) := by
  funext p
  apply propext
  constructor
  · rintro ⟨q,pq,b,hb,eb⟩
    obtain ⟨a,c,ac,ea,ec⟩ := (image_entries_l e full h.graph p q).mp pq
    exact ⟨a,⟨c,ac,inj (eb.trans ec.symm) ▸ hb⟩,ea⟩
  · rintro ⟨a,⟨b,ab,hb⟩,rfl⟩
    exact ⟨e b,(image_entries_l e full h.graph (e a) (e b)).mpr ⟨a,b,ab,rfl,rfl⟩,b,hb,rfl⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 地条件自同构的滤子回拉是背景中的实际集合

只分离背景中给定的条件域；交换图是原模型的一个对象，
因而无需对扩张中的任意谓词作背景分离。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Smem_d.filter_pull_set_l {c X R : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (B T F : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (aut : Aut_d (smdl_structure_l I (R := R) source.1.2.1) B T B F) (K : M.Domain) :
    ∃ L, M.MemberSubset L B.val ∧
      ∀ p : (smdl_structure_l I (R := R) source.1.2.1).Domain,
        M.mem p.val L ↔ Pull_generic_d (smdl_structure_l I (R := R) source.1.2.1) F
          (fun q => M.mem q.val K) p := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  let ρ : Env M 2 := ⟨fun i => [F.val,K].get i,fun _ => K⟩
  let φ : UnarySchema 2 := { body := .existsE (.conj
    (entry_m (.bound 1) .newest (.bound 2)) (.mem .newest (.bound 3))) }
  have sat p : φ.denote ρ p ↔ ∃ q, Entry_d M p q F.val ∧ M.mem q K := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      entry_sat_l M hZF.1,Formula.satisfies_mem_iff]
    rfl
  obtain ⟨L,members⟩ := ZF.separation_exists_d hZF φ ρ B.val
  refine ⟨L,fun p hp => ((members p).mp hp).1,fun p => ?_⟩
  apply ((members p.val).trans (and_congr_right fun _ => sat p.val)).trans
  constructor
  · rintro ⟨_,q,pq,hq⟩
    obtain ⟨a,b,ab,ap,bq⟩ := (image_entries_l Subtype.val full aut.graph p.val q).mp pq
    exact ⟨b,inj ap ▸ ab,show M.mem b.val K from bq.symm ▸ hq⟩
  · rintro ⟨q,pq,hq⟩
    exact ⟨(image_member_l Subtype.val inj full).mpr (aut.domain p q pq).1,q.val,
      (image_entries_l Subtype.val full aut.graph p.val q.val).mpr ⟨p,q,pq,rfl,rfl⟩,hq⟩

end YesMetaZFC.SetTheory.Internal
