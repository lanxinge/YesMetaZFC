import YesMetaZFC.Model.SetTheory.Internal.FlatPredecessor
import YesMetaZFC.Model.SetTheory.Internal.PowerRelativization

/-! # 任意较低秩层的原满足公式

只以 Vν 为参数，把原前驱满足程序的量词限制到 Vν 的子集。
V(ν+1) 在证明中实际构造，在公式中不作为见证；这保留紧邻秩层的边界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def ft_lower_m {d} (X ω F n r f : Term d) : Formula 1 d :=
  lp_rel_m (ft_prev_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.newest : Term 5)) X
    (Fin.cases f (Fin.cases r (Fin.cases n (Fin.cases F (fun _ => ω)))))

@[simp] theorem ft_lower_closed_l {d} (X ω F n r f : Term d)
    (hX : X.freeSupport = []) (hω : ω.freeSupport = []) (hF : F.freeSupport = [])
    (hn : n.freeSupport = []) (hr : r.freeSupport = []) (hf : f.freeSupport = []) :
    (ft_lower_m X ω F n r f).FreeClosed :=
  lp_rel_closed_l _ (ft_prev_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl) X _ hX
    (Fin.cases hf (Fin.cases hr (Fin.cases hn (Fin.cases hF (fun _ => hω)))))

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem ft_lower_rank_l {d} (ρ : Env M d) (X ω F n r f : Term d) {ν c R a : M.Domain}
    (hω : M.IsOmega (ω.eval ρ)) (hV : V_d I ν (X.eval ρ)) (hων : M.MemberSubset (ω.eval ρ) ν)
    (hm : Smem_d K c (X.eval ρ) R) (ha : Sformula_d K (ω.eval ρ) a (n.eval ρ) (F.eval ρ) (r.eval ρ))
    (hf : M.IsSetFunctionFromTo K (f.eval ρ) (ω.eval ρ) (X.eval ρ)) :
    Formula.satisfies ρ (ft_lower_m X ω F n r f) ↔ Satisfies_d K (ω.eval ρ) c a (f.eval ρ) := by
  obtain ⟨μ, hs⟩ := KP.exists_successor (ZF.modelsKP hZF) ν
  obtain ⟨Y, hW⟩ := ZF.v_exists_l I hZF (KP.successor_isOrdinal (ZF.modelsKP hZF) (v_ordinal_l I hV) hs)
  have power := ZF.v_successor_l I hZF hV hW hs
  have nat : M.MemberSubset (ω.eval ρ) (X.eval ρ) := fun i hi => ZF.v_ordinal_mem_l I hZF hV (hων i hi)
  have hw := (power (ω.eval ρ)).mpr nat
  have hF := (power (F.eval ρ)).mpr (fp_program_rank_l I hZF hω hV hων ha.2.1)
  have hg := (power (f.eval ρ)).mpr (fp_function_rank_l I hZF hω hV hων nat hf)
  have ht := ZF.v_transitive_l I hZF hW
  have hn := ht (ω.eval ρ) hw (n.eval ρ) ha.2.1.1
  have hr := ht (n.eval ρ) hn (r.eval ρ) ha.2.2
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω.eval ρ, hw⟩⟩
  let N := rt_model_l Y ny
  let J := fp_rank_interpretation_l I hZF hω hW hw
  let G : N.Domain := ⟨F.eval ρ, hF⟩
  let l : N.Domain := ⟨n.eval ρ, hn⟩
  let k : N.Domain := ⟨r.eval ρ, hr⟩
  let g : N.Domain := ⟨f.eval ρ, hg⟩
  let η : Env N 5 := ⟨Fin.cases g (Fin.cases k (Fin.cases l (Fin.cases G (fun _ => ⟨ω.eval ρ, hw⟩)))), fun _ => g⟩
  exact (lp_rel_model_l ht ny _ (ft_prev_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl) η ρ X _ power
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))).trans
      ((ft_prev_sat_l J (rt_model_ext_l hZF.1 ht ny) η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).trans
        (ft_prev_source_l I hZF hω hV hW hs hων hw G l k g hm ha hf))

/-- 外层仅需是一个包含 Vν 的秩层；其高度既可极限，也可恰为 ν+1。 -/
theorem ft_lower_source_l {Y η : M.Domain} (hY : V_d I η Y) (ny : Nonempty {x // M.mem x Y})
    {d} (ρ : Env (rt_model_l Y ny) d) (X ω F n r f : Term d) {ν c R a : M.Domain}
    (hω : M.IsOmega (ω.eval ρ).val) (hV : V_d I ν (X.eval ρ).val) (hων : M.MemberSubset (ω.eval ρ).val ν)
    (hm : Smem_d K c (X.eval ρ).val R)
    (ha : Sformula_d K (ω.eval ρ).val a (n.eval ρ).val (F.eval ρ).val (r.eval ρ).val)
    (hf : M.IsSetFunctionFromTo K (f.eval ρ).val (ω.eval ρ).val (X.eval ρ).val) :
    Formula.satisfies ρ (ft_lower_m X ω F n r f) ↔ Satisfies_d K (ω.eval ρ).val c a (f.eval ρ).val := by
  refine (lp_rel_absolute_l (ZF.v_transitive_l I hZF hY) ny _ ρ X _
    (fun x hx => ZF.v_subset_mem_l I hZF hY (X.eval ρ).property hx)).trans ?_
  have read := ft_lower_rank_l hZF (image_env_l (M := rt_model_l Y ny) (N := M) Subtype.val ρ)
    X ω F n r f (ν := ν) (c := c) (R := R) (a := a)
  simp only [eval_image_env_l (M := rt_model_l Y ny) (N := M) Subtype.val] at read
  exact read hω hV hων hm ha hf

end YesMetaZFC.SetTheory.Internal
