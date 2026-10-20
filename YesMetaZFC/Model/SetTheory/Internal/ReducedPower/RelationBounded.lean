import YesMetaZFC.Model.SetTheory.Internal.RelationFunctionCapture
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationSyntax
import YesMetaZFC.SetTheory.CumulativeRelativeClosure

/-! # 原关系后继中的共同有界代表族

原关系函数码与所属源的有界函数逐一对应。方向之一回收新函数码，
另一方向将所属源的原图沿共同低层实现读出；两侧使用同一实际复合图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rr_bounded_functions_l {Y S H N Γ γ k D A t G : M.Domain}
    (ny : ∃ y, M.mem y Y) (ext : Rf_ext_d I Y S) (closed : Rr_closed_d I Y S H)
    (hN : M.TransitiveSet N) (algebra : Sc_algebra_d N)
    (hΓN : M.mem Γ N) (rank : Vr_d N γ Γ) (hγ : M.IsLimitOrdinal γ)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (d a : (smdl_structure_l I (R := S) ny).Domain)
    (hD : Rd_entry_d D d.val k) (hA : Rd_entry_d A a.val k) (ht : M.IsRestrictionOf I t k D)
    (hG : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) ny).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) ny).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f)) :
    ∀ g, (M.mem g G ∧ ∀ s y, Rd_entry_d s y g → Rd_entry_d y a.val S) ↔
      ∃ F, M.mem F N ∧ Fn0_d D A F ∧ Cp0_d D Γ Y F k g := by
  have hΓ := rank.transitive_l hZF hN hΓN
  have hDG := fk.1.input_mem_of_pairMember hD
  have hAG := fk.1.input_mem_of_pairMember hA
  have en := ext.native_l I ny
  have ft := fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo fk.1 (hΓ D hDG))
  have key := fn0_of_function_l (ZF.modelsKP hZF) fk.1
  have code {F : M.Domain} {f : (smdl_structure_l I (R := S) ny).Domain}
      (fn : Fn0_d D A F) (hFf : Rd_entry_d F f.val k)
      (g : M.Domain) (fg : Fn0_d D Y g) :
      (∀ s (x y : (smdl_structure_l I (R := S) ny).Domain), Rd_entry_d s x.val t →
        (Rd_entry_d s y.val g ↔ Rd_entry_d x y f)) ↔ Cp0_d D Γ Y F k g := by
    obtain ⟨ff, read⟩ := rr_realize_function_l I hZF.1 hΓ ny ext fk pred a d f hA hD hFf fn
    constructor
    · intro decode
      refine ⟨fg, fun s hs => ?_⟩
      obtain ⟨v, hv, hsv⟩ := fn.2.1 s hs
      obtain ⟨y, hy, hvy⟩ := fk.1.2.2 v (hΓ A hAG v hv)
      obtain ⟨x, hx, hsx⟩ := ft.2.1 s hs
      exact ⟨v, hΓ A hAG v hv, y, hy, hsv, hvy, (decode s ⟨x, hx⟩ ⟨y, hy⟩ hsx).mpr
        ((rf_val_native_l I ny en ..).mp (read s v x y hsv ((ht.2 s x).mp hsx).2 hvy))⟩
    · intro comp s x y hsx
      obtain ⟨v, hv, hsv⟩ := fn.2.1 s (ft.bound_l hsx).1
      obtain ⟨z, hz, hvz⟩ := fk.1.2.2 v (hΓ A hAG v hv)
      have value := (rf_val_native_l I ny en x ⟨z, hz⟩ f).mp
        (read s v x.val z hsv ((ht.2 s x.val).mp hsx).2 hvz)
      have bound := fn.mono_target_l (hΓ A hAG)
      have graph := (comp.value_l bound key hsv).mpr hvz
      constructor
      · intro h
        have eq : (⟨z, hz⟩ : (smdl_structure_l I (R := S) ny).Domain) = y :=
          Subtype.ext (fg.2.2 s (ft.bound_l hsx).1 z hz y.val y.property graph h)
        exact eq ▸ value
      · intro h
        exact congrArg Subtype.val (ff.2.2 x (ff.bound_l h).1 ⟨z, hz⟩ (ff.bound_l value).2 y (ff.bound_l h).2 value h) ▸ graph
  intro g
  constructor
  · rintro ⟨hg, bounded⟩
    obtain ⟨fg, B', f, ff, decode⟩ := (hG g).mp hg
    have ff' : Fn0_d d a f := ff.retarget_l (fun x y hxy => by
      obtain ⟨s, hs, hsx⟩ := (pred D d.val hD x.val).mp (ff.bound_l hxy).1
      exact bounded s y.val ((decode s x y ((ht.2 s x.val).mpr ⟨hs, hsx⟩)).mpr hxy))
    obtain ⟨P, hP, product⟩ := algebra.product D A (hN Γ hΓN D hDG) (hN Γ hΓN A hAG)
    have hPG := rank.relation_mem_l hZF hN hΓN hγ hDG hAG hP (fun z hz => (product z).mp hz)
    obtain ⟨F, hF, hFf, fn⟩ := rr_capture_function_l hZF ny ext closed hΓ fk image pred d a f hD hA hPG product ff'
    exact ⟨F, hN Γ hΓN F hF, fn, (code fn hFf g fg).mp decode⟩
  · rintro ⟨F, hF, fn, comp⟩
    have hFG := rank.relation_mem_l hZF hN hΓN hγ hDG hAG hF fn.1
    obtain ⟨f, hf, hFf⟩ := fk.1.2.2 F hFG
    obtain ⟨ff, _⟩ := rr_realize_function_l I hZF.1 hΓ ny ext fk pred a d ⟨f, hf⟩ hA hD hFf fn
    refine ⟨(hG g).mpr ⟨comp.1, a, ⟨f, hf⟩, ff, (code (f := ⟨f, hf⟩) fn hFf g comp.1).mpr comp⟩, fun s y hsy => ?_⟩
    obtain ⟨v, hv, hsv⟩ := fn.2.1 s (comp.1.bound_l hsy).1
    exact (pred A a.val hA y).mpr ⟨v, hv, (comp.value_l (fn.mono_target_l (hΓ A hAG)) key hsv).mp hsy⟩

end YesMetaZFC.SetTheory.Internal
