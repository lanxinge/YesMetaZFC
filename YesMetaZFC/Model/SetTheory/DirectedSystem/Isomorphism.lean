import YesMetaZFC.Model.SetTheory.DirectedSystem.Relative

/-! # 定向极限中关系嵌入锥的唯一因子 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem di_factor_embedding_l (hZF : M.Models ZF) {J L A p T R q C S Y f : M.Domain}
    {relation : M.Domain → M.Domain → Prop}
    (h : Di_system_d J L A p T R) (limit : Di_limit_d A p T R q C S) (hf : Fn0_d A Y f)
    (comm : ∀ x y u v, Rd_entry_d x y T → Rd_entry_d x u f → Rd_entry_d y v f → u = v)
    (fiber : ∀ x y i u v, Rd_entry_d x i p → Rd_entry_d y i p → Rd_entry_d x u f → Rd_entry_d y v f →
      (x = y ↔ u = v) ∧ (Rd_entry_d x y R ↔ relation u v)) :
    ∃ g, M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) g C Y ∧
      (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y g) ∧
      (∀ B D u v, Rd_entry_d B u g → Rd_entry_d D v g → (Rd_entry_d B D S ↔ relation u v)) ∧
      ∀ k, Fn0_d C Y k → (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y k) → k = g := by
  obtain ⟨g, hg, law, unique⟩ := di_factor_l hZF h limit hf comm
  have push x B y (hx : Rd_entry_d x B q) (hy : Rd_entry_d B y g) : Rd_entry_d x y f := by
    obtain ⟨z, _, hxz⟩ := hf.2.1 x (limit.projection.bound_l hx).1
    exact (fn0_function_l (ZF.modelsKP hZF) hg).1.2 B z y (law x B z hx hxz) hy ▸ hxz
  have future B D u v (hB : Rd_entry_d B u g) (hD : Rd_entry_d D v g) :
      ∃ x y i, Rd_entry_d x B q ∧ Rd_entry_d y D q ∧ Rd_entry_d x i p ∧ Rd_entry_d y i p ∧
        Rd_entry_d x u f ∧ Rd_entry_d y v f := by
    obtain ⟨x, hx⟩ := (limit.range B).mp (hg.bound_l hB).1
    obtain ⟨y, hy⟩ := (limit.range D).mp (hg.bound_l hD).1
    obtain ⟨i, a, b, hai, hbi, hxa, hyb⟩ := h.common_l (limit.projection.bound_l hx).1 (limit.projection.bound_l hy).1
    obtain ⟨E, _, haE⟩ := limit.projection.2.1 a (h.bound x a hxa).2
    obtain ⟨H, _, hbH⟩ := limit.projection.2.1 b (h.bound y b hyb).2
    have e := (limit.kernel x a B E hx haE).mpr ⟨a, hxa, h.identity a (h.bound x a hxa).2⟩
    have d := (limit.kernel y b D H hy hbH).mpr ⟨b, hyb, h.identity b (h.bound y b hyb).2⟩
    exact ⟨a, b, i, e.symm ▸ haE, d.symm ▸ hbH, hai, hbi,
      push a B u (e.symm ▸ haE) hB, push b D v (d.symm ▸ hbH) hD⟩
  refine ⟨g, ⟨fn0_function_l (ZF.modelsKP hZF) hg, ?_⟩, law, ?_, unique⟩
  · intro B D u hB hD
    obtain ⟨x, y, i, hx, hy, hxi, hyi, hxu, hyu⟩ := future B D u u hB hD
    exact (fn0_function_l (ZF.modelsKP hZF) limit.projection).1.2 x B D hx
      (((fiber x y i u u hxi hyi hxu hyu).1.mpr rfl).symm ▸ hy)
  · intro B D u v hB hD
    obtain ⟨x, y, i, hx, hy, hxi, hyi, hxu, hyv⟩ := future B D u v hB hD
    exact (limit.relation x y B D hx hy).trans ((h.rel_at_l hxi hyi
      (h.identity x (limit.projection.bound_l hx).1) (h.identity y (limit.projection.bound_l hy).1)).trans
        (fiber x y i u v hxi hyi hxu hyv).2)

end YesMetaZFC.SetTheory.Internal

/-! ## 直接极限沿实际同构传递

同构后的规范投影仍有完全相同的核与代表关系，故保持同一个定向系统
的直接极限证书。这里只消费实际函数图、双射和关系等价，不用选择公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

theorem di_limit_iso_l {A p T R q C S Y V e r : M.Domain} (limit : Di_limit_d A p T R q C S)
    (he : M.IsSetBijectionFromTo I e C Y) (hr : Fn0_d A Y r)
    (rs : ∀ a y, Rd_entry_d a y r ↔ M.mem a A ∧ ∃ x, Rd_entry_d a x q ∧ Rd_entry_d x y e)
    (rel : M.IsSetRelationOn I V Y)
    (atom : ∀ x y u v, Rd_entry_d x u e → Rd_entry_d y v e → (Rd_entry_d x y S ↔ Rd_entry_d u v V)) :
    Di_limit_d A p T R r Y V := by
  refine ⟨hr, fun y => ⟨?_, fun ⟨a, ha⟩ => (hr.bound_l ha).2⟩, ?_, ?_, rel.2, rel.1⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := he.2 y hy
    obtain ⟨a, hax⟩ := (limit.range x).mp hx
    exact ⟨a, (rs a y).mpr ⟨(limit.projection.bound_l hax).1, x, hax, hxy⟩⟩
  · intro a b u v hau hbv
    obtain ⟨_, x, hax, hxu⟩ := (rs a u).mp hau
    obtain ⟨_, y, hby, hyv⟩ := (rs b v).mp hbv
    exact (⟨fun eq => he.1.2 x y v (eq ▸ hxu) hyv,
      fun eq => he.1.1.1.2 y u v (eq ▸ hxu) hyv⟩ : u = v ↔ x = y).trans (limit.kernel a b x y hax hby)
  · intro a b u v hau hbv
    obtain ⟨_, x, hax, hxu⟩ := (rs a u).mp hau
    obtain ⟨_, y, hby, hyv⟩ := (rs b v).mp hbv
    exact (atom x y u v hxu hyv).symm.trans (limit.relation a b x y hax hby)

end YesMetaZFC.SetTheory.Internal
