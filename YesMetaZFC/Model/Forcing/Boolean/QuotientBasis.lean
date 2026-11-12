import YesMetaZFC.Model.Forcing.Boolean.QuotientTrace
import YesMetaZFC.Model.Forcing.Check.Order
import YesMetaZFC.SetTheory.Card.Basic

/-! # 中间商的旧条件表示及其大小界

载体为主正则开像仍属于商的旧条件。它在中间模型内从 j(C) 分离，
大小直接由旧条件域的实际单射限制得到，不对正则开代数本身作大小假设。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

structure Qb_d (j : M.Domain → N.Domain) (C R Γ : M.Domain) (D B S F : N.Domain) : Prop where
  carrier : ∀ x, N.mem x B ↔ ∃ p, M.mem p C ∧ j p = x ∧ ∃ Y, Entry_d M p Y Γ ∧ N.mem (j Y) D
  order : ∀ x y, Entry_d N x y S ↔ N.mem x B ∧ N.mem y B ∧ Entry_d N x y (j R)
  graph : ∀ x y, Entry_d N x y F ↔ N.mem x B ∧ Entry_d N x y (j Γ)

theorem Qb_d.old_l {j : M.Domain → N.Domain} (inj : Function.Injective j) {C R Γ : M.Domain} {D B S F : N.Domain}
    (k : Qb_d j C R Γ D B S F) (p : M.Domain) :
    N.mem (j p) B ↔ M.mem p C ∧ ∃ Y, Entry_d M p Y Γ ∧ N.mem (j Y) D := by
  apply (k.carrier (j p)).trans
  exact ⟨fun ⟨q,hq,eq,rest⟩ => inj eq ▸ ⟨hq,rest⟩,fun h => ⟨p,h.1,rfl,h.2⟩⟩

theorem quotient_basis_l (hM : M.Models ZF) (hN : N.Models ZF)
    (j : M.Domain → N.Domain) (inj : Function.Injective j)
    (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    {C R z L Γ : M.Domain} (O : Cond_order_d M C R z)
    (fn : M.IsSetFunctionFromTo (kpair_interpretation_l M hM.1 (KP.exists_pair (ZF.modelsKP hM))) Γ C L) (D : N.Domain) :
    ∃ B S F, Qb_d j C R Γ D B S F ∧ Cond_order_d N B S B ∧
      N.IsSetFunctionFromTo (kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))) F B D := by
  let I := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have imageFn := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) j inj full fn
  let ρ : Env N 2 := ⟨Fin.cases (j Γ) (fun _ => D),fun _ => D⟩
  let φ : UnarySchema 2 := { body := .existsE (.conj (entry_m (.bound 1) .newest (.bound 2)) (.mem .newest (.bound 3))) }
  obtain ⟨B,members⟩ := ZF.separation_exists_d hN φ ρ (j C)
  have read x : N.mem x B ↔ N.mem x (j C) ∧ ∃ y, Entry_d N x y (j Γ) ∧ N.mem y D := by
    apply (members x).trans (and_congr_right fun _ => ?_)
    simp only [φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,entry_sat_l N hN.1,Formula.satisfies_mem_iff]
    rfl
  have carrier x : N.mem x B ↔ ∃ p, M.mem p C ∧ j p = x ∧ ∃ Y, Entry_d M p Y Γ ∧ N.mem (j Y) D := by
    apply (read x).trans
    constructor
    · rintro ⟨hx,y,xy,yd⟩
      obtain ⟨p,hp,rfl⟩ := (full C x).mp hx
      obtain ⟨Y,_,rfl⟩ := (full L y).mp (imageFn.output_mem_of_pairMember xy)
      exact ⟨p,hp,rfl,Y,(entry p Y Γ).mpr xy,yd⟩
    · rintro ⟨p,hp,rfl,Y,pY,YD⟩
      exact ⟨(image_member_l j inj full).mpr hp,j Y,(entry p Y Γ).mp pY,YD⟩
  have preord : Preord_d N B (j R) := by
    constructor
    · intro x hx
      obtain ⟨p,hp,rfl,_⟩ := (carrier x).mp hx
      exact (entry p p R).mp (O.refl p hp)
    · intro x y z hx hy hz xy yz
      obtain ⟨p,hp,rfl,_⟩ := (carrier x).mp hx
      obtain ⟨q,hq,rfl,_⟩ := (carrier y).mp hy
      obtain ⟨r,hr,rfl,_⟩ := (carrier z).mp hz
      exact (entry p r R).mp (O.trans p q r hp hq hr ((entry p q R).mpr xy) ((entry q r R).mpr yz))
  obtain ⟨S,order,OS,_,_⟩ := preord_order_l hN preord
  obtain ⟨F,cut⟩ := ZF.exists_restriction hN I (j Γ) B
  have restricted := cut.isSetFunctionFromTo imageFn (fun x hx => ((read x).mp hx).1)
  have function : N.IsSetFunctionFromTo I F B D := ⟨restricted.1,restricted.2.1,fun x hx => by
    obtain ⟨_,y,xy,yd⟩ := (read x).mp hx
    exact ⟨y,yd,(cut.2 x y).mpr ⟨hx,xy⟩⟩⟩
  exact ⟨B,S,F,⟨carrier,order,cut.2⟩,OS,function⟩

theorem Qb_d.size_l (hM : M.Models ZF) (hN : N.Models ZF) {j : M.Domain → N.Domain}
    (inj : Function.Injective j) (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    {C R Γ X κ : M.Domain} {D B S F : N.Domain} (k : Qb_d j C R Γ D B S F)
    (sub : M.MemberSubset C X)
    (size : M.CardinalLessOrEqual (kpair_interpretation_l M hM.1 (KP.exists_pair (ZF.modelsKP hM))) X κ) :
    N.CardinalLessOrEqual (kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))) B (j κ) := by
  let I := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))
  obtain ⟨f,hf⟩ := size
  have image := image_injection_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) j inj full hf
  have bound : N.MemberSubset B (j X) := by
    intro x hx
    obtain ⟨p,hp,rfl,_⟩ := (k.carrier x).mp hx
    exact (image_member_l j inj full).mpr (sub p hp)
  obtain ⟨g,cut⟩ := ZF.exists_restriction hN I (j f) B
  exact ⟨g,cut.isSetFunctionFromTo image.1 bound,fun x y z xz yz =>
    image.2 x y z ((cut.2 x z).mp xz).2 ((cut.2 y z).mp yz).2⟩

end YesMetaZFC.Model.Forcing.Internal
