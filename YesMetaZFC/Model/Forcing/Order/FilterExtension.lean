import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.Forcing.Embedding.Rank
import YesMetaZFC.Model.Forcing.Boolean.GroundGeneric

/-! # 环境中的实际滤子给出另一成员满扩张中的泛型

两侧使用同一个原条件域。滤子的序性质由原条件逐点传输；覆盖目标全部
全局稠密集时，局部要求经全局化与相容性读出，得到完整目标泛型性。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v w
variable {N : Structure.{u}} {M : Structure.{v}} {E : Structure.{w}}
variable (hN : N.Models ZF) (hM : Extensional M) (hE : E.Models ZF)
  (k : N.Domain → M.Domain) (ki : Function.Injective k)
  (kf : ∀ a y, M.mem y (k a) ↔ ∃ t, N.mem t a ∧ k t = y)
  (e : N.Domain → E.Domain) (ei : Function.Injective e)
  (ef : ∀ a y, E.mem y (e a) ↔ ∃ t, N.mem t a ∧ e t = y)
include hN hM hE ki kf ei ef

theorem Gset_d.extension_generic_l {B R z : N.Domain} {D H : M.Domain}
    (O : Cond_order_d N B R z) (filter : Gset_d (k B) (k R) (k z) D H)
    (hits : ∀ C, Dense_set_d E (e B) (e R) (e z) C → ∃ p, M.mem (k p) H ∧ E.mem (e p) C) :
    Generic_d E (e B) (e R) (e z) (Em_generic_d e (fun p => M.mem (k p) H)) := by
  have km {a b : N.Domain} : M.mem (k a) (k b) ↔ N.mem a b := image_member_l k ki kf
  have em {a b : N.Domain} : E.mem (e a) (e b) ↔ N.mem a b := image_member_l e ei ef
  have ke := image_entry_iff_l k ki kf (KP.exists_pair (ZF.modelsKP hN)) hM
  have ee := image_entry_iff_l e ei ef (KP.exists_pair (ZF.modelsKP hN)) hE.1
  have order := image_cond_order_l (ZF.modelsKP hN) hE.1 e ei ef O
  let G := Em_generic_d e (fun p => M.mem (k p) H)
  have proper p (hp : G p) : E.mem p (e B) ∧ p ≠ e z := by
    obtain ⟨a,ha,rfl⟩ := hp
    exact ⟨em.mpr (km.mp (filter.proper (k a) ha).1),fun eq => (filter.proper (k a) ha).2 (congrArg k (ei eq))⟩
  have directed p q (hp : G p) (hq : G q) : ∃ r, G r ∧ Entry_d E r p (e R) ∧ Entry_d E r q (e R) := by
    obtain ⟨a,ha,rfl⟩ := hp
    obtain ⟨b,hb,rfl⟩ := hq
    obtain ⟨r,hr,ra,rb⟩ := filter.directed (k a) (k b) ha hb
    obtain ⟨s,_,rfl⟩ := (kf B r).mp (filter.proper r hr).1
    exact ⟨e s,⟨s,hr,rfl⟩,(ee s a R).mp ((ke s a R).mpr ra),(ee s b R).mp ((ke s b R).mpr rb)⟩
  refine ⟨proper,?_,?_,directed,?_⟩
  · obtain ⟨a,ha⟩ := filter.inhabited
    obtain ⟨p,_,rfl⟩ := (kf B a).mp (filter.proper a ha).1
    exact ⟨e p,p,ha,rfl⟩
  · rintro p q ⟨a,ha,rfl⟩ hq pq
    obtain ⟨b,hb,rfl⟩ := (ef B q).mp hq
    exact ⟨b,filter.upward (k a) (k b) ha (km.mpr hb) ((ke a b R).mp ((ee a b R).mpr pq)),rfl⟩
  · intro p hp C dense
    obtain ⟨D,global,read⟩ := dense_globalize_l hE order (proper p hp).1 dense
    obtain ⟨q,hq,qD⟩ := hits D global
    have qG : G (e q) := ⟨q,hq,rfl⟩
    rcases ((read (e q)).mp qD).2.2 with no | hit
    · obtain ⟨r,hr,rq,rp⟩ := directed (e q) p qG hp
      exact (no ⟨r,⟨(proper r hr).1,(proper r hr).2,rq⟩,rp⟩).elim
    · exact ⟨e q,qG,hit.2⟩

end YesMetaZFC.Model.Forcing.Internal
