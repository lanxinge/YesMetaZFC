import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.SetTheory.Card.CantorBernstein

/-! # 源内 Cantor–Bernstein 构造

在源内所有闭集之间取最小闭集，再分段使用给定单射及反向单射的逆关系。
证明只需源的全分离与有界图构造；不假定源满足 ZF，也不要求相对幂集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_cantor_bernstein_l {ω c X R A B f g : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hA : M.mem A X) (hB : M.mem B X) (hfX : M.mem f X) (hgX : M.mem g X)
    (hf : M.IsSetInjectionFromTo I f A B) (hg : M.IsSetInjectionFromTo I g B A) :
    ∃ k, M.mem k X ∧ M.IsSetBijectionFromTo I k A B := by
  let closed (C : M.Domain) := M.IsCantorBernsteinClosed I f g A B C
  let ρ : Env M 4 := ⟨Fin.cases g (Fin.cases f (Fin.cases B (fun _ => A))), fun _ => A⟩
  let φ : UnarySchema 4 := {
    body := .conj (Formula.forallMem (.bound 4) (.imp
      (.neg (Formula.existsMem (.bound 4) (rd_entry0_m .newest (.bound 1) (.bound 3)))) (.mem .newest (.bound 1))))
      (Formula.forallMem .newest (Formula.forallMem (.bound 4) (Formula.forallMem (.bound 6)
        (.imp (rd_entry0_m (.bound 2) (.bound 1) (.bound 5))
          (.imp (rd_entry0_m (.bound 1) .newest (.bound 4)) (.mem .newest (.bound 3))))))) }
  have delta : φ.body.IsDelta0 := .conj
    (.forallMem _ (.imp (.neg (.existsMem _ (rd_entry0_delta_l ..))) (.mem ..)))
    (.forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.mem ..))))))
  have cs D : φ.denote ρ D ↔ closed D := by
    simp only [φ, UnarySchema.denote, closed, Structure.IsCantorBernsteinClosed, Formula.satisfies_conj_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1]
    exact ⟨fun h => ⟨h.1, fun a b x ha hab hbx => h.2 a ha b (hf.1.output_mem_of_pairMember hab)
      x (hg.1.output_mem_of_pairMember hbx) hab hbx⟩,
      fun h => ⟨h.1, fun a ha b _ x _ hab hbx => h.2 a b x ha hab hbx⟩⟩
  let ne : Nonempty {a // M.mem a X} := ⟨⟨A, hA⟩⟩
  let N := rt_model_l X ne
  have params : ∀ i, M.mem (ρ.bound i) X := Fin.cases hgX (Fin.cases hfX (Fin.cases hB (fun _ => hA)))
  let η : Env N 4 := ⟨fun i => ⟨ρ.bound i, params i⟩, fun _ => ⟨A, hA⟩⟩
  let e : Fin 5 → Fin 6 := Fin.cases 0 (fun i => i.succ.succ)
  let ψ : UnarySchema 4 := {
    body := .forallE (.imp (φ.body.rename e) (.mem (.bound 1) .newest))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have point (a D : N.Domain) : Formula.satisfies ((η.push a).push D) (φ.body.rename e) ↔ closed D.val :=
    (Formula.satisfies_rename ..).trans ((rt_model_delta_l hX ne delta _).trans
      ((Formula.closed_env_l φ.body φ.freeClosed (funext (Fin.cases rfl (fun _ => rfl)))).trans (cs D.val)))
  have read (a : N.Domain) : ψ.denote η a ↔ ∀ D, M.mem D X → closed D → M.mem a.val D := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, point, Formula.satisfies_mem_iff]
    exact ⟨fun h D hd => h ⟨D, hd⟩, fun h D => h D.val D.property⟩
  obtain ⟨C, hC, ca, spec⟩ := sc_separate_relative_l I hZF hω hX hm theory ne ψ η hA
  have members a : M.mem a C ↔ M.mem a A ∧ ∀ D, M.mem D X → closed D → M.mem a D := by
    constructor
    · intro ha
      exact ⟨ca a ha, (read ⟨a, hX C hC a ha⟩).mp ((spec ⟨a, hX C hC a ha⟩).mp ha).2⟩
    · rintro ⟨ha, h⟩
      exact (spec ⟨a, hX A hA a ha⟩).mpr ⟨ha, (read ⟨a, hX A hA a ha⟩).mpr h⟩
  have cc : closed C := by
    refine ⟨fun a ha no => (members a).mpr ⟨ha, fun D _ hd => hd.1 a ha no⟩, ?_⟩
    intro a b x ha hab hbx
    exact (members x).mpr ⟨hg.1.output_mem_of_pairMember hbx,
      fun D hd closed => closed.2 a b x (((members a).mp ha).2 D hd closed) hab hbx⟩
  -- 最小闭集还满足 C = 无反向原像的点 ∪ (g ∘ f)''C；只需源内这个具体候选集。
  let θ : UnarySchema 4 := {
    body := .disj (.neg (Formula.existsMem (.bound 3) (rd_entry0_m .newest (.bound 1) (.bound 2))))
      (Formula.existsMem (.bound 4) (Formula.existsMem (.bound 4)
        (.conj (rd_entry0_m (.bound 1) .newest (.bound 4)) (rd_entry0_m .newest (.bound 2) (.bound 3))))) }
  let ξ : Env M 4 := ⟨Fin.cases g (Fin.cases f (Fin.cases B (fun _ => C))), fun _ => A⟩
  have ts x : θ.denote ξ x ↔ (¬ ∃ b, M.mem b B ∧ Rd_entry_d b x g) ∨
      ∃ a, M.mem a C ∧ ∃ b, M.mem b B ∧ Rd_entry_d a b f ∧ Rd_entry_d b x g := by
    simp only [θ, UnarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨D, hD, ds⟩ := sc_separate_source_l I hZF hω hX hm theory θ
    (.disj (.neg (.existsMem _ (rd_entry0_delta_l ..))) (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))
    ξ (Fin.cases hgX (Fin.cases hfX (Fin.cases hB (fun _ => hC)))) hA
  have dc x (hx : M.mem x D) : M.mem x C := by
    obtain ⟨ha, h⟩ := (ds x).mp hx
    exact ((ts x).mp h).elim (cc.1 x ha) (fun ⟨a, ha, b, _, hab, hbx⟩ => cc.2 a b x ha hab hbx)
  have dd : closed D := by
    refine ⟨fun x hx no => (ds x).mpr ⟨hx, (ts x).mpr (Or.inl no)⟩, ?_⟩
    intro a b x ha hab hbx
    exact (ds x).mpr ⟨hg.1.output_mem_of_pairMember hbx,
      (ts x).mpr (Or.inr ⟨a, dc a ha, b, hf.1.output_mem_of_pairMember hab, hab, hbx⟩)⟩
  let value a b := M.IsCantorBernsteinValue I f g C a b
  have unique a b d (hb : value a b) (hd : value a d) : b = d := by
    rcases hb with ⟨hc, hb⟩ | ⟨hc, hb⟩ <;> rcases hd with ⟨hc', hd⟩ | ⟨hc', hd⟩
    · exact hf.1.1.2 a b d hb hd
    · exact (hc' hc).elim
    · exact (hc hc').elim
    · exact hg.2 b d a hb hd
  let χ : BinarySchema 3 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 2)) (rd_entry0_m (.bound 1) .newest (.bound 3)))
      (.conj (.neg (.mem (.bound 1) (.bound 2))) (rd_entry0_m .newest (.bound 1) (.bound 4))) }
  let ζ : Env M 3 := ⟨Fin.cases C (Fin.cases f (fun _ => g)), fun _ => C⟩
  have vs a b : χ.denote ζ a b ↔ value a b := by
    simp only [χ, BinarySchema.denote, value, Structure.IsCantorBernsteinValue,
      Formula.satisfies_disj_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_neg_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨k, hk, fn, select⟩ := sc_uniform_source_l hZF hω hX hm theory χ
    (.disj (.conj (.mem ..) (rd_entry0_delta_l ..)) (.conj (.neg (.mem ..)) (rd_entry0_delta_l ..)))
    ζ (Fin.cases hC (Fin.cases hfX (fun _ => hgX))) hA hB (fun a ha => by
      classical
      by_cases hc : M.mem a C
      · obtain ⟨b, hb, hab⟩ := hf.1.2.2 a ha
        exact ⟨b, hb, (vs a b).mpr (Or.inl ⟨hc, hab⟩)⟩
      · have pre : ∃ b, M.mem b B ∧ Rd_entry_d b a g := Classical.byContradiction (fun no => hc (cc.1 a ha no))
        obtain ⟨b, hb, hba⟩ := pre
        exact ⟨b, hb, (vs a b).mpr (Or.inr ⟨hc, hba⟩)⟩)
  have realize a b (ha : M.mem a A) (hv : value a b) : Rd_entry_d a b k := by
    obtain ⟨d, _, had⟩ := fn.2.1 a ha
    exact unique a d b ((vs a d).mp (select a d had)) hv ▸ had
  refine ⟨k, hk, ⟨fn0_function_l (ZF.modelsKP hZF) fn, ?_⟩, ?_⟩
  · intro a d b ha hd
    rcases (vs a b).mp (select a b ha) with ⟨hc, hab⟩ | ⟨hc, hba⟩ <;>
      rcases (vs d b).mp (select d b hd) with ⟨hc', hdb⟩ | ⟨hc', hbd⟩
    · exact hf.2 a d b hab hdb
    · exact (hc' (cc.2 a b d hc hab hbd)).elim
    · exact (hc (cc.2 d b a hc' hdb hba)).elim
    · exact hg.1.1.2 b a d hba hbd
  · intro b hb
    obtain ⟨a, ha, hba⟩ := hg.1.2.2 b hb
    classical
    by_cases hc : M.mem a C
    · obtain ⟨_, h⟩ := (ds a).mp (((members a).mp hc).2 D hD dd)
      rcases (ts a).mp h with no | ⟨x, hx, b', _, hxb, hb'a⟩
      · exact (no ⟨b, hb, hba⟩).elim
      · have eq := hg.2 b' b a hb'a hba
        subst b'
        exact ⟨x, ca x hx, realize x b (ca x hx) (Or.inl ⟨hx, hxb⟩)⟩
    · exact ⟨a, ha, realize a b ha (Or.inr ⟨hc, hba⟩)⟩

end YesMetaZFC.SetTheory.Internal
