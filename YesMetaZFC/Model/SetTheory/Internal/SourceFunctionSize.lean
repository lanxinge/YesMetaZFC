import YesMetaZFC.Model.SetTheory.Internal.SourceSmall

/-! # 源内函数与其图的编号

在已有图中读取坐标，把定义域的单射编号传给函数图，或反向传回定义域。
编号的目标可以是任意源内集合；不要求它是基数或序数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_graph_numbering_l {ω c Z R μ A B ι j : M.Domain}
    (hω : M.IsOmega ω) (hZ : M.TransitiveSet Z) (hm : Smem_d I c Z R)
    (theory : Sc_theory_d I ω Z R) (hμZ : M.mem μ Z) (hA : M.mem A Z) (hB : M.mem B Z)
    (hιZ : M.mem ι Z) (hjZ : M.mem j Z) (hι : M.IsSetInjectionFromTo I ι A μ) (hj : Fn0_d A B j) :
    ∃ η, M.mem η Z ∧ M.IsSetInjectionFromTo I η j μ := by
  let ρ : Env M 3 := ⟨Fin.cases A (Fin.cases B (fun _ => ι)), fun _ => A⟩
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 4)
      (.conj (kpair0_m (.bound 3) (.bound 1) .newest) (rd_entry0_m (.bound 1) (.bound 2) (.bound 6)))) }
  have sat p i : φ.denote ρ p i ↔ ∃ x, M.mem x A ∧ ∃ y, M.mem y B ∧ KPair_d M p x y ∧ Rd_entry_d x i ι := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨η, hηZ, hf, select⟩ := sc_uniform_source_l hZF hω hZ hm theory φ
    (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..))))
    ρ (Fin.cases hA (Fin.cases hB (fun _ => hιZ))) hjZ hμZ (fun p hp => by
      obtain ⟨x, hx, y, hy, hpair⟩ := hj.1 p hp
      obtain ⟨i, hi, hxi⟩ := hι.1.2.2 x hx
      exact ⟨i, hi, (sat p i).mpr ⟨x, hx, y, hy, hpair, hxi⟩⟩)
  refine ⟨η, hηZ, fn0_function_l (ZF.modelsKP hZF) hf, fun p q i hpi hqi => ?_⟩
  obtain ⟨x, _, y, _, hp, hxi⟩ := (sat p i).mp (select p i hpi)
  obtain ⟨z, _, v, _, hq, hzi⟩ := (sat q i).mp (select q i hqi)
  have eq := hι.2 x z i hxi hzi
  subst z
  have eq := (fn0_function_l (ZF.modelsKP hZF) hj).1.2 x y v
    ⟨p, hp, (hf.bound_l hpi).1⟩ ⟨q, hq, (hf.bound_l hqi).1⟩
  subst v
  exact kpair_unique_l M hZF.1 hp hq

theorem sc_domain_numbering_l {ω c Z R μ A B η j : M.Domain}
    (hω : M.IsOmega ω) (hZ : M.TransitiveSet Z) (hm : Smem_d I c Z R)
    (theory : Sc_theory_d I ω Z R) (hμZ : M.mem μ Z) (hA : M.mem A Z) (hB : M.mem B Z)
    (hηZ : M.mem η Z) (hjZ : M.mem j Z) (hη : M.IsSetInjectionFromTo I η j μ) (hj : Fn0_d A B j) :
    ∃ ι, M.mem ι Z ∧ M.IsSetInjectionFromTo I ι A μ := by
  let ρ : Env M 3 := ⟨Fin.cases j (Fin.cases B (fun _ => η)), fun _ => j⟩
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 4)
      (.conj (kpair0_m (.bound 1) (.bound 3) .newest) (rd_entry0_m (.bound 1) (.bound 2) (.bound 6)))) }
  have sat x i : φ.denote ρ x i ↔ ∃ p, M.mem p j ∧ ∃ y, M.mem y B ∧ KPair_d M p x y ∧ Rd_entry_d p i η := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨ι, hιZ, hf, select⟩ := sc_uniform_source_l hZF hω hZ hm theory φ
    (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..))))
    ρ (Fin.cases hjZ (Fin.cases hB (fun _ => hηZ))) hA hμZ (fun x hx => by
      obtain ⟨y, hy, p, hp, hpj⟩ := hj.2.1 x hx
      obtain ⟨i, hi, hpi⟩ := hη.1.2.2 p hpj
      exact ⟨i, hi, (sat x i).mpr ⟨p, hpj, y, hy, hp, hpi⟩⟩)
  refine ⟨ι, hιZ, fn0_function_l (ZF.modelsKP hZF) hf, fun x z i hxi hzi => ?_⟩
  obtain ⟨p, _, y, _, hp, hpi⟩ := (sat x i).mp (select x i hxi)
  obtain ⟨q, _, v, _, hq, hqi⟩ := (sat z i).mp (select z i hzi)
  exact (kpair_injective_l M (hη.2 p q i hpi hqi ▸ hp) hq).1

end YesMetaZFC.SetTheory.Internal
