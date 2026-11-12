import YesMetaZFC.Model.Forcing.Boolean.GroundGeneric
import YesMetaZFC.Model.Forcing.Truth.OrderCongruence

/-! # 实际小泛型名字的局部力迫证书

将原条件域、原序、排除值及原幂集一起作规范名称。真实名字值若为地模型
泛型，真值引理给出原泛型内的局部证书；证书反过来约束每个通过该条件的泛型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def gn_body_m : Formula 1 5 := gset_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest

theorem gn_body_closed_l : gn_body_m.FreeClosed := gset_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl

def Gn_d (B R z b Q T w 𝒟 τ p : M.Domain) : Prop := Name_d M B τ ∧
  ∃ A S v D, Check_d M b Q A ∧ Check_d M b T S ∧ Check_d M b w v ∧ Check_d M b 𝒟 D ∧
    Forces_d M B R z gn_body_m ⟨Fin.cases τ (Fin.cases D (Fin.cases v (Fin.cases S (fun _ => A)))),fun _ => τ⟩ p

def gn_force_m {n} (B R z p A S v D τ : Term n) : Formula 1 n :=
  force_at_m gn_body_m (Fin.cases τ (Fin.cases D (Fin.cases v (Fin.cases S (fun _ => A))))) B R z p

@[simp] theorem gn_force_closed_l {n} (B R z p A S v D τ : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hp : p.freeSupport = []) (hA : A.freeSupport = []) (hS : S.freeSupport = [])
    (hv : v.freeSupport = []) (hD : D.freeSupport = []) (hτ : τ.freeSupport = []) :
    (gn_force_m B R z p A S v D τ).FreeClosed :=
  force_at_closed_l _ _ _ _ _ _ gn_body_closed_l
    (Fin.cases hτ (Fin.cases hD (Fin.cases hv (Fin.cases hS (fun _ => hA))))) hB hR hz hp

def gn_m {n} (B R z b Q T w 𝒟 τ p : Term n) : Formula 1 n := set[n] ⟪
  ⌜name_m⌝ₚ(⌜B⌝ₛ,⌜τ⌝ₛ) ∧ (∃ A, ∃ S, ∃ v, ∃ D,
    ⌜check_m⌝ₚ(⌜b⌝ₛ,⌜Q⌝ₛ,A) ∧ ⌜check_m⌝ₚ(⌜b⌝ₛ,⌜T⌝ₛ,S) ∧
    ⌜check_m⌝ₚ(⌜b⌝ₛ,⌜w⌝ₛ,v) ∧ ⌜check_m⌝ₚ(⌜b⌝ₛ,⌜𝒟⌝ₛ,D) ∧
    ⌜gn_force_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜p⌝ₛ,A,S,v,D,⌜τ⌝ₛ))⟫
derive_free_closed gn_m

theorem gn_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z b Q T w 𝒟 τ p : Term n) :
    Formula.satisfies ρ (gn_m B R z b Q T w 𝒟 τ p) ↔
      Gn_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (Q.eval ρ) (T.eval ρ)
        (w.eval ρ) (𝒟.eval ρ) (τ.eval ρ) (p.eval ρ) := by
  simp only [gn_m,Gn_d,Formula.satisfies_conj_iff,Formula.satisfies_exists_iff,
    name_sat_l M hE,check_sat_l M hE,gn_force_m,force_at_sat_l,Definitional.Term.eval_weaken]
  refine and_congr_right fun _ => exists_congr fun A => exists_congr fun S => exists_congr fun v =>
    exists_congr fun D => and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => ?_
  exact forces_env_l hE gn_body_m gn_body_closed_l _ _ (fun i => by
    refine Fin.cases ?_ (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) i
    exact by simp only [Fin.cases_zero,Definitional.Term.eval_weaken]) _

variable (hZF : M.Models ZF) {B R z b Q T w 𝒟 τ p : M.Domain} (O : Cond_order_d M B R z)
include O

theorem Gn_d.value_l (h : Gn_d B R z b Q T w 𝒟 τ p) (power : M.IsPowerSetOf 𝒟 Q)
    {G : M.Domain → Prop} (generic : Generic_d M B R z G) (hp : G p)
    {H : (extension_l M hZF B R z G).Domain} (value : Qval_d M B R z G τ H)
    (j : M.Domain → (extension_l M hZF B R z G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF B R z G).mem y (j a) ↔ ∃ c, M.mem c a ∧ j c = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M B R z G t (j a)) :
    Generic_d M Q T w (fun q => (extension_l M hZF B R z G).mem (j q) H) := by
  obtain ⟨_,A,S,v,D,hA,hS,hv,hD,forced⟩ := h
  let ρ : Env M 5 := ⟨Fin.cases τ (Fin.cases D (Fin.cases v (Fin.cases S (fun _ => A)))),fun _ => τ⟩
  let η : Env (extension_l M hZF B R z G) 5 :=
    ⟨Fin.cases H (Fin.cases (j 𝒟) (Fin.cases (j w) (Fin.cases (j T) (fun _ => j Q)))),fun _ => H⟩
  have values : Env_val_d hZF ρ η := by
    intro t
    cases t with
    | free _ => exact value
    | bound i => exact Fin.cases value (Fin.cases (checks 𝒟 D hD)
        (Fin.cases (checks w v hv) (Fin.cases (checks T S hS) (fun _ => checks Q A hA)))) i
  have truth := (forcing_truth_l O hZF generic gn_body_m gn_body_closed_l ρ η values).mp ⟨p,hp,forced⟩
  exact ((gset_sat_l (extension_ext_l O hZF generic) η _ _ _ _ _).mp truth).ground_l
    hZF (extension_ext_l O hZF generic) j inj full power

theorem gn_of_value_l {G : M.Domain → Prop} (generic : Generic_d M B R z G) (hb : G b)
    {H : (extension_l M hZF B R z G).Domain} (value : Qval_d M B R z G τ H)
    (j : M.Domain → (extension_l M hZF B R z G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF B R z G).mem y (j a) ↔ ∃ c, M.mem c a ∧ j c = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M B R z G t (j a))
    (small : Generic_d M Q T w (fun q => (extension_l M hZF B R z G).mem (j q) H))
    (bound : ∀ y, (extension_l M hZF B R z G).mem y H → (extension_l M hZF B R z G).mem y (j Q)) :
    ∃ p, G p ∧ Entry_d M p b R ∧ Gn_d B R z b Q T w 𝒟 τ p := by
  have hbB := (generic.proper b hb).1
  obtain ⟨A,hA,_,_⟩ := zf_check_l M hZF hbB Q
  obtain ⟨S,hS,_,_⟩ := zf_check_l M hZF hbB T
  obtain ⟨v,hv,_,_⟩ := zf_check_l M hZF hbB w
  obtain ⟨D,hD,_,_⟩ := zf_check_l M hZF hbB 𝒟
  let ρ : Env M 5 := ⟨Fin.cases τ (Fin.cases D (Fin.cases v (Fin.cases S (fun _ => A)))),fun _ => τ⟩
  let η : Env (extension_l M hZF B R z G) 5 :=
    ⟨Fin.cases H (Fin.cases (j 𝒟) (Fin.cases (j w) (Fin.cases (j T) (fun _ => j Q)))),fun _ => H⟩
  have values : Env_val_d hZF ρ η := by
    intro t
    cases t with
    | free _ => exact value
    | bound i => exact Fin.cases value (Fin.cases (checks 𝒟 D hD)
        (Fin.cases (checks w v hv) (Fin.cases (checks T S hS) (fun _ => checks Q A hA)))) i
  have truth : Formula.satisfies η gn_body_m :=
    (gset_sat_l (extension_ext_l O hZF generic) η _ _ _ _ _).mpr
      (image_gset_l hZF (extension_ext_l O hZF generic) j inj full small (fun y =>
        ⟨fun hy => ((full Q y).mp (bound y hy)).elim fun q hq => ⟨q,hq.2.symm ▸ hy,hq.2⟩,
          fun ⟨q,hq,eq⟩ => eq ▸ hq⟩))
  obtain ⟨q,hq,forced⟩ := (forcing_truth_l O hZF generic gn_body_m gn_body_closed_l ρ η values).mpr truth
  obtain ⟨p,hp,pq,pb⟩ := generic.directed q b hq hb
  have lower := (formula_eval_l O hZF generic gn_body_m gn_body_closed_l ρ η values).1.1
  exact ⟨p,hp,pb,qval_name_l value,A,S,v,D,hA,hS,hv,hD,
    lower q p (generic.proper q hq).1 ⟨(generic.proper p hp).1,(generic.proper p hp).2,pq⟩ forced⟩

end YesMetaZFC.Model.Forcing.Internal
