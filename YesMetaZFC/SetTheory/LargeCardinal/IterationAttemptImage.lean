import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptRelative

/-! # 同一联合尝试树沿实际初等图搬运

参数依次为 ω、T、Q、G、枚举、目标、隶属关系、根、指定图、节点集及扩展关系。
像中的节点与严格扩展由原公式读取，输出明确量化目标实际拥有的节点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ja_space_d.image_l {ω κ K X R μ K' Y S c d j : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω μ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (ρ η : Env M 11) (hw : ρ.bound 0 = ω) (images : ∀ i, Rd_entry_d (ρ.bound i) (η.bound i) j)
    (space : Ja_space_d I ω (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4)
      (ρ.bound 5) (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) (ρ.bound 10)) :
    (∀ s, M.mem s Y → (M.mem s (η.bound 9) ↔ Ja_cell_d I ω (η.bound 1) (η.bound 2)
      (η.bound 3) (η.bound 4) (η.bound 5) (η.bound 6) (η.bound 7) (η.bound 8) s)) ∧
    (∀ s t, M.mem s Y → M.mem t Y → (Rd_entry_d t s (η.bound 10) ↔
      M.mem s (η.bound 9) ∧ M.mem t (η.bound 9) ∧ Ja_extend_d (η.bound 1) s t)) := by
  let x : Nonempty {a // M.mem a X} := ⟨⟨ω, source.omega_mem⟩⟩
  let y : Nonempty {a // M.mem a Y} := ⟨⟨ω, target.omega_mem⟩⟩
  let ρ' : Env (rt_model_l X x) 11 :=
    ⟨fun i => ⟨ρ.bound i, hj.1.1.input_mem_of_pairMember (images i)⟩, fun _ => ⟨ω, source.omega_mem⟩⟩
  let η' : Env (rt_model_l Y y) 11 :=
    ⟨fun i => ⟨η.bound i, hj.1.1.output_mem_of_pairMember (images i)⟩, fun _ => ⟨ω, target.omega_mem⟩⟩
  have fixed := hj.omega_l I hZF source.omega source.transitive target.transitive hm hn source.omega_mem
  have hw' := hj.1.1.1.2 ω (η.bound 0) ω (hw ▸ images 0) fixed
  let a (i : Fin 11) : Term 11 := .bound i
  let φ : Formula 1 11 := set[11] ⟪
    (∀ s, s ∈ ⌜a 9⌝ₛ ↔ ⌜ja_cell_m⌝ₚ(⌜a 0⌝ₛ, ⌜a 1⌝ₛ, ⌜a 2⌝ₛ, ⌜a 3⌝ₛ,
      ⌜a 4⌝ₛ, ⌜a 5⌝ₛ, ⌜a 6⌝ₛ, ⌜a 7⌝ₛ, ⌜a 8⌝ₛ, s)) ∧
    (∀ s t, ⌜rd_entry0_m⌝ₚ(t, s, ⌜a 10⌝ₛ) ↔
      s ∈ ⌜a 9⌝ₛ ∧ t ∈ ⌜a 9⌝ₛ ∧ ⌜ja_extend_m⌝ₚ(⌜a 1⌝ₛ, s, t))⟫
  have read {κ K Z R} (src : Ep_source_d hZF ω κ K Z R) (nz : Nonempty {s // M.mem s Z})
      (θ : Env (rt_model_l Z nz) 11) (hw : (θ.bound 0).val = ω) : Formula.satisfies θ φ ↔
      (∀ s : (rt_model_l Z nz).Domain, M.mem s.val (θ.bound 9).val ↔ Ja_cell_d I ω
        (θ.bound 1).val (θ.bound 2).val (θ.bound 3).val (θ.bound 4).val (θ.bound 5).val
        (θ.bound 6).val (θ.bound 7).val (θ.bound 8).val s.val) ∧
      (∀ s t : (rt_model_l Z nz).Domain, Rd_entry_d t.val s.val (θ.bound 10).val ↔
        M.mem s.val (θ.bound 9).val ∧ M.mem t.val (θ.bound 9).val ∧ Ja_extend_d (θ.bound 1).val s.val t.val) := by
    have entry {b} (ζ : Env (rt_model_l Z nz) b) (s t f : Term b) : Formula.satisfies ζ (rd_entry0_m s t f) ↔
        Rd_entry_d (s.eval ζ).val (t.eval ζ).val (f.eval ζ).val := by
      simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
        (rt_model_delta_l src.transitive nz (rd_entry0_delta_l s t f) ζ).trans (rd_entry0_sat_l hZF.1 ..)
    simp only [φ, a, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, src.ja_cell_l hZF nz, ja_extend_relative_l hZF.1 src.transitive nz,
      entry, Definitional.Term.eval_weaken, Term.eval_bound, hw]
    rfl
  obtain ⟨o, ho⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF source.omega ⟨c, R, d, S, hm.empty_pred_l I ho, hn.empty_pred_l I ho, hj⟩
    x y φ (by simp -implicitDefEqProofs [φ, a, Definitional.Formula.FreeClosed]) ρ' η' images
  obtain ⟨nodes, edges⟩ := (read target y η' hw').mp
    (tr.mp ((read source x ρ' hw).mpr ⟨fun s => space.nodes s.val, fun s t => space.edges s.val t.val⟩))
  exact ⟨fun s hs => nodes ⟨s, hs⟩, fun s t hs ht => edges ⟨s, hs⟩ ⟨t, ht⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
