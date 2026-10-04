import YesMetaZFC.SetTheory.InnerModel.Recursion.FunctionGraph

/-! # 内部函数图的有界复合与坐标重排

复合以实际中间值为证书，公式为 Δ₀；KP 的 Σ₁ 函数图构造同时给出复合和
函数空间上的重排图。坐标函数可以重复、遗漏或置换任意内部有限坐标。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem Fn0_d.ext_l (hE : Extensional M) {A B C F G : M.Domain} (hf : Fn0_d A B F) (hg : Fn0_d A C G)
    (he : ∀ a, M.mem a A → ∃ b, Rd_entry_d a b F ∧ Rd_entry_d a b G) : F = G := by
  have sub {B F G} (hf : Fn0_d A B F)
      (he : ∀ a, M.mem a A → ∃ b, Rd_entry_d a b F ∧ Rd_entry_d a b G) : M.MemberSubset F G := by
    intro p hp
    obtain ⟨a, ha, b, hb, hpair⟩ := hf.1 p hp
    obtain ⟨c, hcF, hcG⟩ := he a ha
    have eq := hf.2.2 a ha c (hf.bound_l hcF).2 b hb hcF ⟨p, hpair, hp⟩
    obtain ⟨r, hr, hrG⟩ := (eq ▸ hcG : Rd_entry_d a b G)
    exact kpair_unique_l M hE hr hpair ▸ hrG
  exact hE.eq_of_same_members F G (fun p => ⟨sub hf he p, sub hg (fun a ha =>
    (he a ha).imp fun _ h => h.symm) p⟩)

def Cp0_d (m n K q s t : M.Domain) : Prop := Fn0_d m K t ∧ ∀ i, M.mem i m →
  ∃ r, M.mem r n ∧ ∃ x, M.mem x K ∧ Rd_entry_d i r q ∧ Rd_entry_d r x s ∧ Rd_entry_d i x t

def cp0_m {d} (m n K q s t : Term d) : Formula 1 d := .conj (fn0_m m K t)
  (Formula.forallMem m (Formula.existsMem n.weaken (Formula.existsMem K.weaken.weaken (.conj
    (rd_entry0_m (.bound 2) (.bound 1) q.weaken.weaken.weaken) (.conj
      (rd_entry0_m (.bound 1) .newest s.weaken.weaken.weaken) (rd_entry0_m (.bound 2) .newest t.weaken.weaken.weaken))))))
derive_free_closed cp0_m

theorem cp0_delta_l {d} (m n K q s t : Term d) : (cp0_m m n K q s t).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.existsMem _ (.existsMem _
    (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))

theorem cp0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (m n K q s t : Term d) :
    Formula.satisfies ρ (cp0_m m n K q s t) ↔
      Cp0_d (m.eval ρ) (n.eval ρ) (K.eval ρ) (q.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [cp0_m, Cp0_d, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem cp0_unique_l (hE : Extensional M) {m n K q s t v : M.Domain} (hq : Fn0_d m n q) (hs : Fn0_d n K s)
    (ht : Cp0_d m n K q s t) (hv : Cp0_d m n K q s v) : t = v := by
  apply ht.1.ext_l hE hv.1
  intro i hi
  obtain ⟨r, hr, x, hx, hir, hrx, hix⟩ := ht.2 i hi
  obtain ⟨r', hr', y, hy, hir', hry, hiy⟩ := hv.2 i hi
  have eq := hq.2.2 i hi r' hr' r hr hir' hir
  have eq := hs.2.2 r hr y hy x hx (eq ▸ hry) hrx
  exact ⟨x, hix, eq ▸ hiy⟩

theorem cp0_mono_l {m n K L q s t} (hKL : M.MemberSubset K L) (h : Cp0_d m n K q s t) : Cp0_d m n L q s t :=
  ⟨h.1.mono_target_l hKL, fun i hi => (h.2 i hi).imp fun _ hr => ⟨hr.1,
    hr.2.imp fun x hx => ⟨hKL x hx.1, hx.2⟩⟩⟩

theorem cp0_exists_l (hKP : M.Models KP) {m n K q s : M.Domain} (hq : Fn0_d m n q) (hs : Fn0_d n K s) :
    ∃ t, Cp0_d m n K q s t := by
  let ρ : Env M 3 := ⟨Fin.cases s (Fin.cases q (fun _ => n)), fun _ => n⟩
  let φ : Delta0BinarySchema 3 := {
    body := Formula.existsMem (.bound 4) (.conj (rd_entry0_m (.bound 2) .newest (.bound 4))
      (rd_entry0_m .newest (.bound 1) (.bound 3)))
    delta0 := .existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)) }
  have sat i x : (S1_binary.of_delta0 φ).schema.denote ρ i x ↔
      ∃ r, M.mem r n ∧ Rd_entry_d i r q ∧ Rd_entry_d r x s := by
    rw [S1_binary.of_delta0_sat_l]
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hKP.1]
    rfl
  obtain ⟨t, ht, hp⟩ := s1_function_l hKP (S1_binary.of_delta0 φ) ρ m K (fun i hi => by
    obtain ⟨r, hr, hir⟩ := hq.2.1 i hi
    obtain ⟨x, _, hrx⟩ := hs.2.1 r hr
    exact ⟨x, (sat i x).mpr ⟨r, hr, hir, hrx⟩⟩) (fun i hi x y hx hy => by
      obtain ⟨r, hr, hir, hrx⟩ := (sat i x).mp hx
      obtain ⟨r', hr', hir', hry⟩ := (sat i y).mp hy
      have eq := hq.2.2 i hi r' hr' r hr hir' hir
      exact hs.2.2 r hr x (hs.bound_l hrx).2 y (hs.bound_l hry).2 hrx (eq ▸ hry))
    (fun i _ x hx => ((sat i x).mp hx).elim fun _ hr => (hs.bound_l hr.2.2).2)
  refine ⟨t, ht, fun i hi => ?_⟩
  obtain ⟨x, hx, hix⟩ := ht.2.1 i hi
  obtain ⟨r, hr, hir, hrx⟩ := (sat i x).mp ((hp i x).mp hix).2
  exact ⟨r, hr, x, hx, hir, hrx, hix⟩

/-- 给定实际函数空间，一次内部收集构造全部坐标重排。 -/
theorem cp0_projection_l (hKP : M.Models KP) {m n K q H D} (hq : Fn0_d m n q)
    (hH : ∀ s, M.mem s H ↔ Fn0_d n K s) (hD : ∀ t, M.mem t D ↔ Fn0_d m K t) :
    ∃ p, Fn0_d H D p ∧ ∀ s t, Rd_entry_d s t p ↔ M.mem s H ∧ Cp0_d m n K q s t := by
  let ρ : Env M 4 := ⟨Fin.cases q (Fin.cases K (Fin.cases n (fun _ => m))), fun _ => m⟩
  let φ : Delta0BinarySchema 4 := {
    body := cp0_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := cp0_delta_l .. }
  have sat s t : (S1_binary.of_delta0 φ).schema.denote ρ s t ↔ Cp0_d m n K q s t :=
    (S1_binary.of_delta0_sat_l ..).trans (cp0_sat_l hKP.1 ..)
  obtain ⟨p, hp, hs⟩ := s1_function_l hKP (S1_binary.of_delta0 φ) ρ H D
    (fun s hs => (cp0_exists_l hKP hq ((hH s).mp hs)).imp fun t ht => (sat s t).mpr ht)
    (fun s hs t v ht hv => cp0_unique_l hKP.1 hq ((hH s).mp hs) ((sat s t).mp ht) ((sat s v).mp hv))
    (fun s _ t ht => (hD t).mpr ((sat s t).mp ht).1)
  exact ⟨p, hp, fun s t => (hs s t).trans (and_congr_right fun _ => sat s t)⟩

end YesMetaZFC.SetTheory.InnerModel
