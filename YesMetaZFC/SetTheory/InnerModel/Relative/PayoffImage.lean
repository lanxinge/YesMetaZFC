import YesMetaZFC.SetTheory.InnerModel.Relative.PayoffModelMinimum
import YesMetaZFC.SetTheory.InnerModel.Relative.TruthSyntax
import YesMetaZFC.Model.SetTheory.Images.OrdinalSequenceImage
import YesMetaZFC.Model.Forcing.Ground.TreeShift

/-! # 同一较低 Jensen 层上的收益运输

成员满嵌入保持真实递归层、规范序数代码和层内完整真值。反向只需原
层号及序数参数有实际原像，即在源中构造同代码、同收益的呈示。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (e : M.Domain → N.Domain) (ei : Function.Injective e)
  (ef : ∀ a y, N.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include ei ef

theorem Jp_d.image_l {φ : Formula 1 4} (hc : φ.FreeClosed) {S B a c A : M.Domain}
    (present : Jp_d I φ S B a c A) : Jp_d J φ (e S) (e B) (e a) (e c) (e A) := by
  obtain ⟨γ,q,U,code,layer,hB,ha,hq,values⟩ := present
  have mem {x y : M.Domain} := @image_member_l M N e ei ef x y
  have params x : (fun i => e (Fin.cases B (Fin.cases a (Fin.cases q (Fin.cases x Fin.elim0))) i)) =
      Fin.cases (e B) (Fin.cases (e a) (Fin.cases (e q) (Fin.cases (e x) Fin.elim0))) :=
    funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  refine ⟨e γ,e q,e U,oc_pair_image_l hM hN e ei ef code,
    ⟨image_ord_l hM hN e ei ef layer.1,ja_value_image_l e ei ef layer.2⟩,
    mem.mpr hB,mem.mpr ha,mem.mpr hq,fun y => ⟨?_,?_⟩⟩
  · intro hy
    obtain ⟨x,hx,rfl⟩ := (ef A y).mp hy
    obtain ⟨hb,truth⟩ := (values x).mp hx
    exact ⟨mem.mpr hb,params x ▸ (st_image_l e ei ef U φ hc _).mp truth⟩
  · rintro ⟨hy,truth⟩
    obtain ⟨x,hx,rfl⟩ := (ef B y).mp hy
    exact mem.mpr ((values x).mpr ⟨hx,(st_image_l e ei ef U φ hc _).mpr ((params x).symm ▸ truth)⟩)

/-- 层号和序数参数的实际原像足以在源中构造原收益，无须假定收益有原像。 -/
theorem jp_pull_l {φ : Formula 1 4} (hc : φ.FreeClosed) {S B a γ q : M.Domain} {c A U : N.Domain}
    (oγ : M.IsOrdinal γ) (oq : M.IsOrdinal q)
    (code : Oc_pair_d J (e γ) (e q) c) (layer : Ja_d (e S) (e γ) U)
    (hB : N.mem (e B) U) (ha : N.mem (e a) U) (hq : N.mem (e q) U)
    (values : Jp_value_d φ (e B) (e a) (e q) U A) :
    ∃ c' A', Jp_d I φ S B a c' A' ∧ e c' = c ∧ e A' = A := by
  obtain ⟨V,hV⟩ := ja_value_exists_l S (ZF.models_kpi_l hM) γ
  have eqV : e V = U := ja_value_unique_l (e S) (ZF.models_kpi_l hN)
    (ja_value_image_l e ei ef hV) layer.2
  have mem {x y : M.Domain} := @image_member_l M N e ei ef x y
  obtain ⟨c',code'⟩ := oc_pair_exists_l I hM oγ oq
  obtain ⟨A',define⟩ := jp_value_exists_l (ZF.modelsKP hM) φ hc B a q V
  have present : Jp_d I φ S B a c' A' :=
    ⟨γ,q,V,code',⟨oγ,hV⟩,mem.mp (eqV.symm ▸ hB),mem.mp (eqV.symm ▸ ha),mem.mp (eqV.symm ▸ hq),
      fun x => ⟨fun hx => ⟨define.1 x hx,(define.2 x (define.1 x hx)).mp hx⟩,
        fun hx => (define.2 x hx.1).mpr hx.2⟩⟩
  have eqc := oc_pair_unique_l J hN (oc_pair_image_l hM hN e ei ef code') code
  have image := present.image_l hM hN e ei ef hc
  rw [eqc] at image
  have target : Jp_d J φ (e S) (e B) (e a) c A :=
    ⟨e γ,e q,U,code,layer,hB,ha,hq,fun x =>
      ⟨fun hx => ⟨values.1 x hx,(values.2 x (values.1 x hx)).mp hx⟩,
        fun hx => (values.2 x hx.1).mpr hx.2⟩⟩
  exact ⟨c',A',present,eqc,image.unique_l hN target⟩

end YesMetaZFC.SetTheory.InnerModel.Relative
