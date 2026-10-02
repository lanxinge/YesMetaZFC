import YesMetaZFC.Model.Forcing.Applications.Cohen.Flip
import YesMetaZFC.Model.Forcing.Internal.Homogeneous.Basic

/-! # 任意添加量 Cohen 力迫的弱齐性

在两个有限条件取值不同的公共坐标上翻转第一个条件。差异坐标由原公式分离，
翻转后两条件一致，已有有限并图给出共同加强。全证明只用 ZF。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fn_whom_l {ω X Y o l B R} (hω : M.IsOmega ω) (hY : Pair_d M Y o l)
    (hB : ∀ p, M.mem p B ↔ Fn_d I ω X Y p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p) : Whom_d M B R B := by
  intro p q hp _ hq _
  have hpf := (hB p).mp hp
  have hqf := (hB q).mp hq
  let ρ : Env M 2 := (⟨fun _ => p, fun _ => p⟩ : Env M 1).push q
  let φ : UnarySchema 2 := {
    body := .existsE (.existsE (.conj (entry_m (.bound 2) (.bound 1) (.bound 4))
      (.conj (entry_m (.bound 2) .newest (.bound 3)) (.neg (Formula.extensionalEq (.bound 1) .newest))))) }
  obtain ⟨S, hS⟩ := ZF.separation_exists_d hZF φ ρ X
  have hs a : M.mem a S ↔ M.mem a X ∧ ∃ b c, Entry_d M a b p ∧ Entry_d M a c q ∧ b ≠ c := by
    simpa only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
      entry_sat_l M hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1] using! hS a
  obtain ⟨F, hF, hf⟩ := fn_flip_l hZF hY hB hR S
  obtain ⟨s, hsf, hsn⟩ := cflip_exists_l hZF hY hpf S
  have hps := (hf p s).mpr ⟨hp, hsf⟩
  have agree : Agree_d I s q := by
    intro a b c hab hac
    obtain ⟨d, had, hdb⟩ := (cflip_entry_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hsf a b).mp hab
    have haX := (hpf.1.2 a d had).1
    have hcY := (hqf.1.2 a c hac).2
    have neq (haS : M.mem a S) : d ≠ c := by
      obtain ⟨_, v, w, hav, haw, hvw⟩ := (hs a).mp haS
      have hdv := hpf.1.1.2 a d v had hav
      have hcw := hqf.1.1.2 a c w hac haw
      exact fun h => hvw (hdv.symm.trans (h.trans hcw))
    rcases hdb with ⟨haS, ⟨hd, hb⟩ | ⟨hd, hb⟩⟩ | ⟨haS, hb⟩
    · rcases (hY c).mp hcY with hc | hc
      · exact False.elim (neq haS (hd.trans hc.symm))
      · exact hb.trans hc.symm
    · rcases (hY c).mp hcY with hc | hc
      · exact hb.trans hc.symm
      · exact False.elim (neq haS (hd.trans hc.symm))
    · classical
      have hdc : d = c := Classical.byContradiction (fun hn => haS ((hs a).mpr ⟨haX, d, c, had, hac, hn⟩))
      exact hb.trans hdc
  obtain ⟨r, hr, hrs, hrq⟩ := ZF.fn_union_l I hZF hω hsn hqf agree
  have hrB := (hB r).mpr hr
  exact ⟨F, s, hF, hps, r,
    ⟨hrB, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hrB),
      (hR r s).mpr ⟨hrB, (hB s).mpr hsn, hrs⟩⟩, (hR r q).mpr ⟨hrB, hq, hrq⟩⟩

theorem cohen_whom_l {κ B R} (h : Cohen_spec_d I κ B R) : Whom_d M B R B := by
  obtain ⟨_, _, _, _, _, hω, _, _, hY, _, hB, _, hR⟩ := h
  exact fn_whom_l hZF hω hY hB hR

end YesMetaZFC.Model.Forcing.Internal
