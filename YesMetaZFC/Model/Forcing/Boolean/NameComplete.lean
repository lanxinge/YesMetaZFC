import YesMetaZFC.Model.Forcing.Boolean.NameHomCountable
import YesMetaZFC.Model.Forcing.Boolean.NameHomSyntax
import YesMetaZFC.Model.SetTheory.ProjectReflection

/-! # 原小泛型名字诱导的完全同态及主核约化

先把实际图与所有参数一同反射到可数初等模型，完成原公式后再反射回来。
公开定理仅要求原 ZF，不要求地模型外部可数、良基或具备额外泛型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Nh_d.complete_l {B R z b p Q T w 𝒟 τ K S e C L V d F : M.Domain}
    (h : Nh_d hZF B R z b p Q T w 𝒟 τ K S e C L V d F) : BooleanZF.Cbh_d I K S e L V d F := by
  let α : Formula 1 18 := nh_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14) (.bound 15) (.bound 16) (.bound 17)
  let β : Formula 1 18 := BooleanZF.cbh_m kpair_convention_l
    (.bound 10) (.bound 11) (.bound 12) (.bound 14) (.bound 15) (.bound 16) (.bound 17)
  have hα : α.FreeClosed := by unfold α; apply nh_m_freeClosed <;> rfl
  have hβ : β.FreeClosed := by unfold β; apply BooleanZF.cbh_m_freeClosed <;> rfl
  let ρ : Env M 18 := ⟨fun i => [B,R,z,b,p,Q,T,w,𝒟,τ,K,S,e,C,L,V,d,F].get i,fun _ => B⟩
  have raw : Formula.satisfies ρ α := (nh_sat_l hZF ρ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr h
  have result := FirstOrderSemantics.countable_consequence_l (Γ := ZF) α β hα hβ (fun N hN f onto η raw => by
    have data := (nh_sat_l hN η _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp raw
    exact (BooleanZF.cbh_sat_l (kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN)))
      hN.1 η _ _ _ _ _ _ _).mpr (data.countable_complete_l hN f onto)) hZF ρ raw
  exact (BooleanZF.cbh_sat_l I hZF.1 ρ _ _ _ _ _ _ _).mp result

/-- 从原名字的实际小泛型值出发，自动取得局部条件和完全同态；旧幂集在内部构造。 -/
theorem gn_value_complete_l {B R z b Q T w τ : M.Domain} (O : Cond_order_d M B R z)
    (smallOrder : Cond_order_d M Q T w) {G : M.Domain → Prop} (generic : Generic_d M B R z G) (hb : G b)
    {Y : (extension_l M hZF B R z G).Domain} (value : Qval_d M B R z G τ Y)
    (j : M.Domain → (extension_l M hZF B R z G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF B R z G).mem y (j a) ↔ ∃ c, M.mem c a ∧ j c = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M B R z G t (j a))
    (small : Generic_d M Q T w (fun q => (extension_l M hZF B R z G).mem (j q) Y))
    (bound : ∀ y, (extension_l M hZF B R z G).mem y Y → (extension_l M hZF B R z G).mem y (j Q)) :
    ∃ p 𝒟 K S e C L V d F, G p ∧ Nh_d hZF B R z b p Q T w 𝒟 τ K S e C L V d F ∧
      BooleanZF.Cbh_d I K S e L V d F := by
  obtain ⟨𝒟,power⟩ := ZF.exists_powerSet hZF Q
  obtain ⟨p,hp,pb,name⟩ := gn_of_value_l hZF (𝒟 := 𝒟) O generic hb value j inj full checks small bound
  obtain ⟨K,S,e,C,L,V,d,F,data⟩ := nh_exists_l hZF O smallOrder (generic.proper b hb).1
    (generic.proper p hp).1 (generic.proper p hp).2 pb power name
  exact ⟨p,𝒟,K,S,e,C,L,V,d,F,hp,data,data.complete_l hZF⟩

theorem gn_complete_kernel_l {B R z b p Q T w 𝒟 τ : M.Domain} (O : Cond_order_d M B R z)
    (small : Cond_order_d M Q T w) (hb : M.mem b B) (hp : M.mem p B) (hz : p ≠ z)
    (pb : Entry_d M p b R) (power : M.IsPowerSetOf 𝒟 Q) (name : Gn_d B R z b Q T w 𝒟 τ p) :
    ∃ K S e C L V d F N k u A J,
      Nh_d hZF B R z b p Q T w 𝒟 τ K S e C L V d F ∧ BooleanZF.Cbh_d I K S e L V d F ∧
      (∀ a, M.mem a N ↔ M.mem a K ∧ Entry_d M a d F) ∧ BooleanZF.Bsup_d I K S N k ∧
      Entry_d M k d F ∧ BooleanZF.Imp_d I K S k e u ∧ BooleanZF.Bi_d I K S u A ∧
      M.IsRestrictionOf I J F A ∧ BooleanZF.Cba_d I A S e ∧ BooleanZF.Cbh_d I A S e L V d J ∧
      M.IsSetInjectionFromTo I J A L ∧
      (∀ a, M.mem a K → (Entry_d M a d F ↔ Entry_d M a k S)) ∧
      (∀ a b x y, Entry_d M a x J → Entry_d M b y J → (Entry_d M x y V ↔ Entry_d M a b S)) ∧
      ∀ a y, Entry_d M a y F → ∃ c, Entry_d M c y J := by
  obtain ⟨K,S,e,C,L,V,d,F,data⟩ := nh_exists_l hZF O small hb hp hz pb power name
  have complete := data.complete_l hZF
  obtain ⟨N,k,u,A,J,kernel,sup,zero,neg,carrier,cut,algebra,reduced,inj,principal,reflects,range⟩ :=
    complete.kernel_l I hZF data.source data.target.toBoolean_d
  exact ⟨K,S,e,C,L,V,d,F,N,k,u,A,J,data,complete,kernel,sup,zero,neg,⟨neg.1,carrier⟩,
    cut,algebra,reduced,inj,principal,reflects,range⟩

end YesMetaZFC.Model.Forcing.Internal
