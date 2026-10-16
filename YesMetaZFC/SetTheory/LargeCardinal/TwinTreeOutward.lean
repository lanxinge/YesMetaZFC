import YesMetaZFC.SetTheory.LargeCardinal.TwinTreeCertificate

/-! # 同一双树胜策在传递外模型中保持

目标重新构造其全部对局和正树投影收益集，策略及反例树秩仍是原对象的像。
I 的情形用目标中的两树覆盖；II 的情形仅凭反例树秩即可排除正树投影。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "K" => kp_pair_l (ZF.modelsKP hN)
include hi he

/-- 输出同一 e(σ) 的目标获胜性；目标只需 ZF，I 的分支才使用覆盖。 -/
theorem Td_winner_d.outward_l {b : Bool} {ω A Y F T Z G S H J B W σ : M.Domain}
    (hw : M.IsOmega ω) (space : Fseq_space_d I ω Y F) (tree : Tree_d F T)
    (space' : Fseq_space_d I ω Z G) (tree' : Tree_d G S)
    (winner : Td_winner_d hM b ω A Y F T Z G S H J B W σ)
    (cover : b = true → Td_cover_d K (e ω) (e A) (e Y) (e F) (e T) (e Z) (e G) (e S)) :
    ∃ B' W', Td_winner_d hN b (e ω) (e A) (e Y) (e F) (e T) (e Z) (e G) (e S) (e H) (e J) B' W' (e σ) := by
  have hwN := image_omega_l (hEN := hN.1) e hi he hM
    (fun _ hn => KP.mem_minimal_exists_d (ZF.modelsKP hN) hn) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e ω))
  have hist := image_fseq_l hM hN e hi he hw hwN winner.finite
  have finite := image_fseq_l hM hN e hi he hw hwN space
  have finite' := image_fseq_l hM hN e hi he hw hwN space'
  have opposite : Fseq_space_d I ω (if b then Z else Y) (if b then G else F) := by
    cases b <;> assumption
  have cert := winner.certificate.image_l hM hN e hi he opposite winner.finite
  have cert' : Tp_certificate_d hN b (e ω) (e A) (if b then e Z else e Y)
      (if b then e G else e F) (if b then e S else e T) (e H) (e J) (e σ) := by
    cases b <;> exact cert
  have turns n : N.mem n (e J) ↔ N.mem n (e ω) ∧ Gm_even_d K (e ω) n := by
    constructor
    · intro hn
      obtain ⟨k, hk, rfl⟩ := (he J n).mp hn
      obtain ⟨hkw, even⟩ := (winner.turns k).mp hk
      exact ⟨(image_member_l e hi he).mpr hkw, (image_even_l hM hN e hi he hw).mp even⟩
    · rintro ⟨hn, even⟩
      obtain ⟨k, hk, rfl⟩ := (he ω n).mp hn
      exact (image_member_l e hi he).mpr ((winner.turns k).mpr
        ⟨hk, (image_even_l hM hN e hi he hw).mpr even⟩)
  obtain ⟨B', runs⟩ := ZF.exists_functionSpace hN K (e ω) (e A)
  obtain ⟨W', payoff⟩ := tp_payoff_l hN (e ω) (e A) (e Y) (e F) (e T) B'
  refine ⟨B', W', hist, runs, turns, payoff, ⟨cert'.1, ?_⟩, cert'⟩
  intro x hx follows
  have fx := (runs x).mp hx
  cases b
  · intro yes
    exact cert'.avoid_l hN hwN finite (image_tree_l e hi he tree) hist fx follows ((payoff x).mp yes).2
  · apply (payoff x).mpr ∘ And.intro hx
    exact (cover rfl x fx).elim id (fun yes =>
      (cert'.avoid_l hN hwN finite' (image_tree_l e hi he tree') hist fx follows yes).elim)

end YesMetaZFC.SetTheory.LargeCardinal
