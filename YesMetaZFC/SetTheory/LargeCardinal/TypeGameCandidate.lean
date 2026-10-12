import YesMetaZFC.SetTheory.LargeCardinal.TypeGameLanguageTransfer
import YesMetaZFC.Model.SetTheory.Internal.TypeDropSource

/-! # 继续分支中同一候选的完整证书

原语言与原 dcp 弹性一起进入新反射层。投影集合在目标内由分离构造，
再用字面唯一性识别两边的 dcp；不假定它已有语义实现。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- 两个新位置为完整候选 u 及元数 m，后十个位置保留原语言。
def tg_candidate0_m : Formula 1 12 := .conj
  (ee_language0_m.rename (fun i => i.succ.succ))
  (tg_elastic_m (.bound 4) (.bound 1) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 0))

theorem tg_candidate0_closed_l : tg_candidate0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_candidate0_m, Definitional.Formula.FreeClosed]

theorem tg_candidate_sat_l (hZFC : M.Models ZFC) (ρ : Env M 12) :
    Formula.satisfies ρ tg_candidate0_m ↔
      Ee_language_d (ZFC.models_zf_l hZFC) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) (ρ.bound 5) (ρ.bound 6) (ρ.bound 7)
        ⟨ρ.bound 8, ρ.bound 9, ρ.bound 10, ρ.bound 11⟩ ∧
      Tg_elastic_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (ρ.bound 4) (ρ.bound 1) (ρ.bound 7)
        ⟨ρ.bound 8, ρ.bound 9, ρ.bound 10, ρ.bound 11⟩ (ρ.bound 0) := by
  simp only [tg_candidate0_m, Formula.satisfies_conj_iff, Formula.satisfies_rename, ee_language0_sat_l hZFC, tg_elastic_sat_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (ZFC.models_zf_l hZFC).1]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X Y η C η' D : M.Domain} (nc : Nonempty {a // M.mem a C}) (ρ : Env (rt_model_l C nc) 12)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

theorem Tg_context_d.candidate_peer_l {r B R x S y T π σ C₀ κ K κ' K' L W : M.Domain}
    (context : Tg_context_d ω X η C) (target : Tg_context_d ω Y η' D)
    (source : Ep_source_d hZF ω κ K X S) (next : Ep_source_d hZF ω κ' K' Y T)
    (bt : M.TransitiveSet B) (mb : Smem_d I r B R) (mx : Smem_d I x X S) (my : Smem_d I y Y T)
    (j : Smap_d I ω r x B X π) (k : Smap_d I ω r y B Y σ) (hwB : M.mem ω B)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (hW : M.mem W X) (rank : Vr_d X L W) (hW' : M.mem W Y) (rank' : Vr_d Y L W)
    (hL : M.IsLimitOrdinal L) (hwW : M.mem ω W) (hkW : M.mem (p 3) W) (hWD : M.mem W D)
    (hw : p 2 = ω) (hu : M.mem (p 0) D) (valid : Formula.satisfies ρ tg_candidate0_m) :
    M.mem (p 1) ω ∧ (∀ i : Fin 10, M.mem (p i.succ.succ) W) ∧
      ∃ nd : Nonempty {a // M.mem a D}, ∃ θ : Env (rt_model_l D nd) 12,
        (∀ i, (θ.bound i).val = p i) ∧ Formula.satisfies θ tg_candidate0_m := by
  obtain ⟨language, elastic⟩ := (Formula.satisfies_conj_iff ..).mp valid
  let χ := Env.reindex ρ (fun i : Fin 10 => i.succ.succ)
  have language : Formula.satisfies χ ee_language0_m := (Formula.satisfies_rename ..).mp language
  obtain ⟨hn, low, nd, χ', same, moved⟩ := context.language_peer_l hZF nc χ target source next
    bt mb mx my j k hwB iC iD hW rank hW' rank' hL hwW hkW hWD hw language
  have fs := (context.read_l hZF source).1
  have ft := (target.read_l hZF next).1
  simp only [tg_elastic_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at elastic
  obtain ⟨v, drop, elastic⟩ := elastic
  have drop := (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair
    (ρ.push v) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mp drop
  have elastic := (ee_elastic_absolute_l fs.transitive nc (ρ.push v)
    (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 0)).mp elastic
  obtain ⟨m, sm, hm⟩ := source.omega.1.2 (p 4) hn
  have eqm := hZF.1.eq_of_same_members m (p 1) (fun a => (sm a).trans (drop.1 a).symm)
  have hmω : M.mem (p 1) ω := eqm ▸ hm
  have hm : M.mem (p 1) D := ft.transitive ω target.omega (p 1) hmω
  have tail (i : Fin 10) : M.mem (p i.succ.succ) D :=
    Eq.mp (congrArg (fun a => M.mem a D) (same i)) (χ'.bound i).property
  have hp : ∀ i : Fin 12, M.mem (p i) D := Fin.cases hu (Fin.cases hm tail)
  let θ : Env (rt_model_l D nd) 12 := ⟨fun i => ⟨p i, hp i⟩, fun _ => ⟨ω, target.omega⟩⟩
  have sameEnv : χ'.bound = (Env.reindex θ (fun i : Fin 10 => i.succ.succ)).bound := by
    funext i
    exact Subtype.ext (same i)
  have lang : Formula.satisfies θ (ee_language0_m.rename (fun i => i.succ.succ)) :=
    (Formula.satisfies_rename ..).mpr ((Formula.closed_env_l ee_language0_m ee_language0_closed_l sameEnv).mp moved)
  obtain ⟨c, Q, model⟩ := smdl_membership_l I hZF ⟨ω, target.omega⟩
  have theory := next.rank_theory_l hZF target.member target.rank target.limit model
  obtain ⟨v', hv, project⟩ := td_project_source_exists_l ft.transitive hZF source.omega model theory
    (hp 4) (hp 1) (hp 7) (hp 0)
  have eqv := project.unique_l I hZF.1 drop.2
  have hv : M.mem v.val D := eqv ▸ hv
  let v₀ : (rt_model_l D nd).Domain := ⟨v.val, hv⟩
  refine ⟨hmω, low, nd, θ, fun _ => rfl, (Formula.satisfies_conj_iff ..).mpr ⟨lang, ?_⟩⟩
  simp only [tg_elastic_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff]
  refine ⟨v₀, ?_, ?_⟩
  · exact (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ft.transitive nd ft.pair
      (θ.push v₀) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mpr drop
  · exact (ee_elastic_absolute_l ft.transitive nd (θ.push v₀)
      (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 0)).mpr elastic

end YesMetaZFC.SetTheory.LargeCardinal
