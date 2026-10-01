import YesMetaZFC.Model.Forcing.Stage.Atomic.Push

/-! # 完全嵌入下等号力迫的反射

目标等号力迫与源约减共同定义内部双模拟。目标匹配条目后，重新选择同时位于
旧源条件与新标签以下的约减，得到源双模拟的实际匹配见证。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {P R z Q S w F : M.Domain}

/-- 目标等号力迫在它的每个源约减上反射；不要求目标条件属于阶段像。 -/
theorem nmap_eq_pull_l (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w)
    (hZF : M.Models ZF) (h : Reg_embed_d M P R z Q S w F) {x y s t p q}
    (hx : Name_d M P x) (hy : Name_d M P y) (hs : Nmap_d M F x s) (ht : Nmap_d M F y t)
    (hp : M.mem p P) (hr : Red_d M R Q S w F q p) (he : Eq_force_d M Q S w q s t) :
    Eq_force_d M P R z p x y := by
  let hI : Mem_ind_d M := check_ind_l M hZF
  let hPair := KP.exists_pair (ZF.modelsKP hZF)
  have names {x a} (ha : Nmap_d M F x a) : Name_d M Q a :=
    nmap_name_l M hZF (fun b c hc => (h.domain b c hc).2.2.1) ha
  obtain ⟨W, hxW, hyW, hW⟩ := name_support_l M hPair (KP.exists_union (ZF.modelsKP hZF)) hx hy
  let ρ : Env M 5 := ((((⟨fun _ => R, fun _ => R⟩ : Env M 1).push Q).push S).push w).push F
  let φ : BinarySchema 6 := {
    body := eq_pull_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨K, hK⟩ := rel_separation_l hZF φ ρ P W
  have hk u a b : Rel_d M K u a b ↔ M.mem u P ∧ M.mem a W ∧ M.mem b W ∧ Eq_pull_d M R Q S w F u a b := by
    simpa only [BinarySchema.denote, φ, eq_pull_sat_l M hZF.1] using! hK u a b
  have symm {u a b} (hab : Rel_d M K u a b) : Rel_d M K u b a := by
    obtain ⟨hu, ha, hb, v, x, y, hax, hby, he, hr⟩ := (hk u a b).mp hab
    exact (hk u b a).mpr ⟨hu, hb, ha, v, y, x, hby, hax,
      eq_force_symm_l hZF (names hax) (names hby) he, hr⟩
  have forth (u a b) (hab : Rel_d M K u a b) : Match_d M false P R z K u a b := by
    obtain ⟨_, haW, hbW, v, x, y, hax, hby, he, hred⟩ := (hk u a b).mp hab
    intro c d hcd r hr hrd
    have hd := (supp_entry_l M hW haW hcd).2
    have hdz : d ≠ z := fun hz => hr.2.1 (O.zero r hr.1 (hz ▸ hrd))
    obtain ⟨d', hdd⟩ := h.total d hd hdz
    obtain ⟨c', hcc⟩ := nmap_exists_l M hZF F c
    have hc'x := (nmap_entry_l M hZF.1 hI hPair hax c' d').mpr ⟨c, d, hcd, hcc, hdd⟩
    obtain ⟨v₀, hrv⟩ := h.total r hr.1 hr.2.1
    obtain ⟨a₀, ha₀, ha₀v⟩ := hred r v₀ hrv hr.2.2
    have ha₀d := L.trans a₀ v₀ d' ha₀.1 (h.domain r v₀ hrv).2.2.1 (h.domain d d' hdd).2.2.1
      ha₀v ((h.order r d v₀ d' hrv hdd).mpr hrd)
    obtain ⟨a₁, e', f', ha₁, he'f, ha₁f, hce⟩ :=
      ((eq_force_unfold_l M hZF (names hax) (names hby)).mp he).2.1 c' d' hc'x a₀ ha₀ ha₀d
    obtain ⟨e, f, hef, hee, hff⟩ := (nmap_entry_l M hZF.1 hI hPair hby e' f').mp he'f
    have ha₁v := L.trans a₁ a₀ v₀ ha₁.1 ha₀.1 (h.domain r v₀ hrv).2.2.1 ha₁.2.2 ha₀v
    obtain ⟨p₀, hp₀, hred₀⟩ := reg_reduce_below_l O L h ha₁.1 ha₁.2.1 hrv ha₁v
    obtain ⟨p₁, hp₁, hp₁f, hred₁⟩ := red_refine_l O L h ha₁.1 hp₀.1 hp₀.2.1 hred₀ hff ha₁f
    exact ⟨p₁, e, f, below_trans_l O hr.1 hp₁ hp₀, hef, hp₁f,
      (hk p₁ c e).mpr ⟨hp₁.1, (supp_entry_l M hW haW hcd).1, (supp_entry_l M hW hbW hef).1,
        a₁, c', e', hcc, hee, hce, hred₁⟩⟩
  refine ⟨hp, K, ?_, (hk p x y).mpr ⟨hp, hxW, hyW, q, s, t, hs, ht, he, hr⟩⟩
  intro u a b hab
  refine ⟨forth u a b hab, ?_⟩
  intro c d hcd r hr hrd
  obtain ⟨j, e, f, hj, hef, hjf, hce⟩ := forth u b a (symm hab) c d hcd r hr hrd
  exact ⟨j, e, f, hj, hef, hjf, symm hce⟩

/-- 名称搬运在阶段像上精确保留并反射原等号力迫。 -/
theorem nmap_eq_l (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w)
    (hZF : M.Models ZF) (h : Reg_embed_d M P R z Q S w F) {x y s t p q}
    (hx : Name_d M P x) (hy : Name_d M P y) (hs : Nmap_d M F x s) (ht : Nmap_d M F y t)
    (hpq : Entry_d M p q F) : Eq_force_d M P R z p x y ↔ Eq_force_d M Q S w q s t :=
  ⟨nmap_eq_push_l O L hZF h hx hy hs ht hpq,
    nmap_eq_pull_l O L hZF h hx hy hs ht (h.domain p q hpq).1 (red_image_l L h hpq)⟩

end YesMetaZFC.Model.Forcing.Internal
