import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRoundScope

/-! # 内层更新产生实际跨模型迭代轮

存在量词的十六个见证一次解包。原实现和弹性保存在同一个相对秩段内，
给定回答的原扩展器进入 nice 树；所需正则性与共同秩段由记录自动取得。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_round_env_d (ρ : Env M 38) (v : Fin 16 → M.Domain) : Env M 54 :=
  ρ.push (v 15) |>.push (v 14) |>.push (v 13) |>.push (v 12) |>.push (v 11) |>.push (v 10)
    |>.push (v 9) |>.push (v 8) |>.push (v 7) |>.push (v 6) |>.push (v 5) |>.push (v 4)
    |>.push (v 3) |>.push (v 2) |>.push (v 1) |>.push (v 0)

theorem tg_successor_read_l (ρ : Env M 38) (seed : Formula.satisfies ρ tg_seed0_m)
    (valid : Formula.satisfies ρ tg_successor0_m) :
    ∃ v : Fin 16 → M.Domain, Formula.satisfies (tg_round_env_d ρ v) tg_round0_m := by
  simp only [tg_successor0_m, tg_successor_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨τ, C, V, Q, w, η, Z, a, H, f₀, f₁, f₂, f₃, q₀, q₁, q₂, valid⟩ := valid
  let v : Fin 16 → M.Domain := fun i => [q₂, q₁, q₀, f₃, f₂, f₁, f₀, H, a, Z, η, w, Q, V, C, τ].get i
  exact ⟨v, (Formula.satisfies_conj_iff ..).mpr ⟨(Formula.satisfies_rename ..).mpr seed, valid⟩⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X η C : M.Domain} (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))
local notation "σ" => (Fin.cases (p 47) (Fin.cases (p 48) (Fin.cases (p 49) (Fin.cases (p 50)
  (Fin.cases (p 51) (Fin.cases (p 52) (fun _ => p 53)))))))

/-- 原回答的扩展器施加到指定树前驱，原类型通过共同极限秩段识别。 -/
theorem Tg_context_d.round_l {c₀ α ξ T J G E H k c d R Y S μ K μ' K' ζ V η₀ C₀ : M.Domain}
    (context : Tg_context_d ω X η C) (prior : Tg_context_d ω Y η₀ C₀)
    (owner : Ic_model_d hZF ω μ K X R) (source : Ic_model_d hZF ω μ' K' Y S)
    (tree : It_pnice_d hZF ω c₀ α T J G E H) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c J) (hd : Rd_entry_d k d J) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (hV : M.mem V X) (rank : Vr_d X ζ V) (hV' : M.mem V Y) (rank' : Vr_d Y ζ V)
    (hζ : M.IsLimitOrdinal ζ) (hVC : M.mem V C₀) (hζδ : M.mem ζ (p 18)) (hκV : M.mem (p 21) V)
    (hw : p 16 = ω)
    (above : ∀ i ν, Rd_entry_d i ν H → M.mem ν (p 39) ∨ ν = p 39)
    (valid : Formula.satisfies ρ tg_round0_m) :
    ∃ β T' J' G' E' H' d' j N R' K₀ L F κ' U' D' u' η' C' W,
        It_pnice_d hZF ω c₀ β T' J' G' E' H' ∧ It_extension_d α ξ k T J G E β T' J' G' E' ∧
        Rd_entry_d α d' J' ∧ It_map_d G' k α j ∧ Smem_d I d' N R' ∧ Ic_model_d hZF ω L K₀ N R' ∧
        It_ultra_d hZF ω (p 21) L F d d' j ∧ Wd_crit_d I Y j (p 21) κ' ∧
        M.IsLimitOrdinal L ∧ M.mem (p 15) L ∧ M.MemberSubset L κ' ∧
        (∀ i μ, Rd_entry_d i μ H' → M.mem μ κ' ∨ μ = κ') ∧
        Rd_entry_d (p 31) U' j ∧ Rd_entry_d (p 32) D' j ∧ Rd_entry_d (p 34) u' j ∧
        Tg_reply_d I ω (p 23) (p 24) κ' (p 15) U' D' (p 12) u' (p 11) (p 36) σ
          (p 38) ⟨p 2, p 1, p 0⟩ ∧
        Rd_entry_d η₀ η' j ∧ Rd_entry_d C₀ C' j ∧ Tg_context_d ω N η' C' ∧
        Tg_reply_in_d ω (p 23) (p 24) κ' (p 15) U' D' (p 12) u' (p 11) (p 36) (p 38)
          (p 2) (p 1) (p 0) σ C' ∧
        M.mem W X ∧ M.mem W C ∧ Vr_d X L W ∧ Er_level_d N L W ∧ M.mem (p 12) W ∧ M.mem (p 11) W ∧
        (∀ μ, M.mem μ L → Ea_agree_d ω μ X N) ∧
        ∃ V₀, M.mem V₀ Y ∧ Vr_d Y (p 21) V₀ ∧ M.mem V₀ N ∧ Vr_d N (p 21) V₀ ∧
          ∀ x, M.mem x V₀ → Rd_entry_d x x j := by
  obtain ⟨hδ, regular, hκ⟩ := context.round_regular_l hZF nc ρ owner hw valid
  obtain ⟨hU, hD, hu⟩ := context.round_members_l hZF nc ρ owner.source hV rank hζ hκV hw valid
  have hκX := owner.source.transitive C context.member (p 21) (ρ.bound 21).property
  obtain ⟨K', ready⟩ := owner.rebase_l hZF hκX (owner.source.omega.subset_limitOrdinal hZF hκ)
    (sc_ordinal_small_l hZF owner.source.omega owner.source.transitive mx owner.source.theory hκX hκ.1)
  have hκY := source.source.transitive V hV' (p 21) hκV
  obtain ⟨K'', priorReady⟩ := source.rebase_l hZF hκY (source.source.omega.subset_limitOrdinal hZF hκ)
    (sc_ordinal_small_l hZF source.source.omega source.source.transitive my source.source.theory hκY hκ.1)
  have data := ((Formula.satisfies_conj_iff ..).mp valid).2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at data
  obtain ⟨hχτ, _, hτδ, _, _, _, _, _, _, _, _, _, _, hb, hz, hs₀, hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, image⟩ := data
  let s : Fin 7 → Term 54 := Fin.cases (.bound 47) (Fin.cases (.bound 48) (Fin.cases (.bound 49)
    (Fin.cases (.bound 50) (Fin.cases (.bound 51) (Fin.cases (.bound 52) (fun _ => .bound 53))))))
  have slots : (fun i => (Definitional.Term.eval ρ (s i)).val) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have finite : ∀ i, M.mem (Definitional.Term.eval ρ (s i)).val ω := by
    intro i
    exact Fin.cases (hw ▸ hs₀) (Fin.cases (hw ▸ hs₁) (Fin.cases (hw ▸ hs₂)
      (Fin.cases (hw ▸ hs₃) (Fin.cases (hw ▸ hs₄) (Fin.cases (hw ▸ hs₅)
        (Fin.cases (hw ▸ hs₆) (fun j => Fin.elim0 j))))))) i
  have oτ := hδ.1.mem hτδ
  have result := context.tree_image_l hZFC nc ρ
    (.bound 16) (.bound 21) (.bound 18) (.bound 23) (.bound 24) (.bound 31) (.bound 32) (.bound 34)
    (.bound 15) (.bound 12) (.bound 11) (.bound 36) (.bound 38) (.bound 2) (.bound 1) (.bound 0) s
    prior ready priorReady tree succ hc hd mx my hw hδ regular hV rank hV' rank' hζ hVC
    (hw ▸ hb) (hw ▸ hz) finite hζδ hκV hU hD hu
    (fun i μ hm => (above i μ hm).elim (oτ.transitive (p 39) hχτ μ)
      (fun eq => eq.symm ▸ hχτ)) image
  rw [slots] at result
  exact result

end YesMetaZFC.SetTheory.LargeCardinal
