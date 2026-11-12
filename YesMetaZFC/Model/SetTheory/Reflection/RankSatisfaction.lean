import YesMetaZFC.Model.SetTheory.Types.FlatSatisfaction
import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax

/-! # Vν 的满足关系在 V(ν+1) 中的单一公式

接口自动核验结构关系、程序、变量域和赋值的秩界。调用方只交付原结构码、
原内部公式码和实际赋值，无须提供源模型公理、真值表或编码见证。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def ft_local_m {d} (Y ω X R F n r f : Term d) : Formula 1 d :=
  lr_rel_m (ft_sat_m (𝒞 := FlatPairing.convention) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.newest : Term 7))
    Y (Fin.cases f (Fin.cases r (Fin.cases n (Fin.cases F (Fin.cases R (Fin.cases X (fun _ => ω)))))))

@[simp] theorem ft_local_closed_l {d} (Y ω X R F n r f : Term d)
    (hY : Y.freeSupport = []) (hω : ω.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hF : F.freeSupport = []) (hn : n.freeSupport = []) (hr : r.freeSupport = []) (hf : f.freeSupport = []) :
    (ft_local_m Y ω X R F n r f).FreeClosed :=
  lr_rel_closed_l _ (ft_sat_m_freeClosed _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl) Y _ hY (Fin.cases hf (Fin.cases hr (Fin.cases hn (Fin.cases hF
    (Fin.cases hR (Fin.cases hX (fun _ => hω)))))))

/-- 所有内部有限公式的统一正确性；ν 可以是后继序数，仅要求 ν≥ω。 -/
theorem ft_rank_satisfaction_l (hZF : M.Models ZF) {d} (ρ : Env M d) (Y ω X R F n r f : Term d)
    {ν μ c a : M.Domain} (hω : M.IsOmega (ω.eval ρ)) (hV : V_d I ν (X.eval ρ)) (hW : V_d I μ (Y.eval ρ))
    (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset (ω.eval ρ) ν)
    (hc : Smdl_d (fp_interpretation_l (ZF.models_kpi_l hZF)) c (X.eval ρ) (R.eval ρ))
    (ha : Sformula_d (fp_interpretation_l (ZF.models_kpi_l hZF)) (ω.eval ρ) a (n.eval ρ) (F.eval ρ) (r.eval ρ))
    (hf : M.IsSetFunctionFromTo (fp_interpretation_l (ZF.models_kpi_l hZF)) (f.eval ρ) (ω.eval ρ) (X.eval ρ)) :
    Formula.satisfies ρ (ft_local_m Y ω X R F n r f) ↔
      Satisfies_d (fp_interpretation_l (ZF.models_kpi_l hZF)) (ω.eval ρ) c a (f.eval ρ) := by
  have pow := ZF.v_successor_l I hZF hV hW hs
  have nat : M.MemberSubset (ω.eval ρ) (X.eval ρ) := fun i hi => ZF.v_ordinal_mem_l I hZF hV (hων i hi)
  have hw := (pow (ω.eval ρ)).mpr nat
  have hx := (pow (X.eval ρ)).mpr (fun _ h => h)
  have hR := (pow (R.eval ρ)).mpr (fp_relation_rank_l I hZF hω hV hων hc.2.2)
  have hF := (pow (F.eval ρ)).mpr (fp_program_rank_l I hZF hω hV hων ha.2.1)
  have hg := (pow (f.eval ρ)).mpr (fp_function_rank_l I hZF hω hV hων nat hf)
  have trans := v_transitive_l I hW
  have hn := trans (ω.eval ρ) hw (n.eval ρ) ha.2.1.1
  have hr := trans (n.eval ρ) hn (r.eval ρ) ha.2.2
  let N := rt_model_l (Y.eval ρ) ⟨⟨ω.eval ρ, hw⟩⟩
  let J := fp_rank_interpretation_l I hZF hω hW hw
  let w : N.Domain := ⟨ω.eval ρ, hw⟩
  let x : N.Domain := ⟨X.eval ρ, hx⟩
  let s : N.Domain := ⟨R.eval ρ, hR⟩
  let t : N.Domain := ⟨F.eval ρ, hF⟩
  let l : N.Domain := ⟨n.eval ρ, hn⟩
  let k : N.Domain := ⟨r.eval ρ, hr⟩
  let g : N.Domain := ⟨f.eval ρ, hg⟩
  let η : Env N 7 := ⟨Fin.cases g (Fin.cases k (Fin.cases l (Fin.cases t (Fin.cases s (Fin.cases x (fun _ => w)))))), fun _ => w⟩
  let φ := ft_sat_m (𝒞 := FlatPairing.convention) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.newest : Term 7)
  have rel := sc_relative_sat_l trans ⟨⟨ω.eval ρ, hw⟩⟩ φ
    (ft_sat_m_freeClosed _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl) η ρ Y
    (Fin.cases f (Fin.cases r (Fin.cases n (Fin.cases F (Fin.cases R (Fin.cases X (fun _ => ω))))))) rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))))
  exact rel.trans ((ft_sat_sat_l J (rt_model_ext_l hZF.1 trans ⟨⟨ω.eval ρ, hw⟩⟩) η
    (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).trans
    (ft_source_satisfaction_l I hZF hω hW hw x s t l k g hV hs hων hc ha hf))

end YesMetaZFC.SetTheory.Internal
