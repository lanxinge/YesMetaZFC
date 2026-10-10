import YesMetaZFC.Model.Forcing.Stage.Atomic.Syntax

/-! # 阶段名称搬运保持等号力迫

把源等号关系搬到阶段像以下，分离为目标名称闭支撑上的实际双模拟。目标加强
先约减到源，再匹配源条目，最后返回目标共同加强；不要求阶段像稠密。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {P R z Q S w F : M.Domain}

theorem nmap_eq_push_l (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w)
    (hZF : M.Models ZF) (h : Reg_embed_d M P R z Q S w F) {x y s t p q}
    (hx : Name_d M P x) (hy : Name_d M P y) (hs : Nmap_d M F x s) (ht : Nmap_d M F y t)
    (hpq : Entry_d M p q F) (he : Eq_force_d M P R z p x y) : Eq_force_d M Q S w q s t := by
  let hI : Mem_ind_d M := check_ind_l M hZF
  let hPair := KP.exists_pair (ZF.modelsKP hZF)
  have names {x a} (ha : Nmap_d M F x a) : Name_d M Q a :=
    nmap_name_l M hZF (fun b c hc => (h.domain b c hc).2.2.1) ha
  obtain ⟨W, hsW, htW, hW⟩ := name_support_l M hPair (KP.exists_union (ZF.modelsKP hZF)) (names hs) (names ht)
  let ρ : Env M 5 := ((((⟨fun _ => P, fun _ => P⟩ : Env M 1).push R).push z).push S).push F
  let φ : BinarySchema 6 := {
    body := eq_push_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨K, hK⟩ := rel_separation_l hZF φ ρ Q W
  have hk u a b : Rel_d M K u a b ↔ M.mem u Q ∧ M.mem a W ∧ M.mem b W ∧ Eq_push_d M P R z S F u a b := by
    simpa only [BinarySchema.denote, φ, eq_push_sat_l M hZF.1] using! hK u a b
  have symm {u a b} (hab : Rel_d M K u a b) : Rel_d M K u b a := by
    obtain ⟨hu, ha, hb, p, v, x, y, hpv, huv, hx, hy, hxa, hyb, he⟩ := (hk u a b).mp hab
    exact (hk u b a).mpr ⟨hu, hb, ha, p, v, y, x, hpv, huv, hy, hx, hyb, hxa,
      eq_force_symm_l hZF hx hy he⟩
  have forth (u a b) (hab : Rel_d M K u a b) : Match_d M false Q S w K u a b := by
    obtain ⟨hu, haW, hbW, p, v, x, y, hpv, huv, hx, hy, hxa, hyb, he⟩ := (hk u a b).mp hab
    intro c d hcd r hr hrd
    obtain ⟨x', d₀, hx'd, hx'c, hdd⟩ := (nmap_entry_l M hZF.1 hI hPair hxa c d).mp hcd
    have hrv := L.trans r u v hr.1 hu (h.domain p v hpv).2.2.1 hr.2.2 huv
    obtain ⟨p₀, hp₀, hr₀⟩ := reg_reduce_below_l O L h hr.1 hr.2.1 hpv hrv
    obtain ⟨p₁, hp₁, hp₁d, hr₁⟩ := red_refine_l O L h hr.1 hp₀.1 hp₀.2.1 hr₀ hdd hrd
    have hp₁p := below_trans_l O (h.domain p v hpv).1 hp₁ hp₀
    obtain ⟨p₂, y', e₀, hp₂, hy'e, hp₂e, hxy⟩ :=
      ((eq_force_unfold_l M hZF hx hy).mp he).2.1 x' d₀ hx'd p₁ hp₁p hp₁d
    obtain ⟨b', hy'b⟩ := nmap_exists_l M hZF F y'
    have he₀ := (name_entry_l M hy hy'e).2
    have he₀z : e₀ ≠ z := fun hz => hp₂.2.1 (O.zero p₂ hp₂.1 (hz ▸ hp₂e))
    obtain ⟨e, he₀e⟩ := h.total e₀ he₀ he₀z
    obtain ⟨v₂, hp₂v⟩ := h.total p₂ hp₂.1 hp₂.2.1
    obtain ⟨j, hj, hjv⟩ := hr₁ p₂ v₂ hp₂v hp₂.2.2
    have hb'e := (nmap_entry_l M hZF.1 hI hPair hyb b' e).mpr ⟨y', e₀, hy'e, hy'b, he₀e⟩
    have hje := L.trans j v₂ e hj.1 (h.domain p₂ v₂ hp₂v).2.2.1 (h.domain e₀ e he₀e).2.2.1
      hjv ((h.order p₂ e₀ v₂ e hp₂v he₀e).mpr hp₂e)
    exact ⟨j, b', e, hj, hb'e, hje, (hk j c b').mpr
      ⟨hj.1, (supp_entry_l M hW haW hcd).1, (supp_entry_l M hW hbW hb'e).1,
        p₂, v₂, x', y', hp₂v, hjv, (name_entry_l M hx hx'd).1, (name_entry_l M hy hy'e).1,
        hx'c, hy'b, hxy⟩⟩
  have hq := (h.domain p q hpq).2.2
  refine ⟨hq.1, K, ?_, (hk q s t).mpr ⟨hq.1, hsW, htW,
    p, q, x, y, hpq, L.refl q hq.1, hx, hy, hs, ht, he⟩⟩
  intro u a b hab
  refine ⟨forth u a b hab, ?_⟩
  intro c d hcd r hr hrd
  obtain ⟨j, e, f, hj, hef, hjf, hce⟩ := forth u b a (symm hab) c d hcd r hr hrd
  exact ⟨j, e, f, hj, hef, hjf, symm hce⟩

end YesMetaZFC.Model.Forcing.Internal
