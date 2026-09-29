import YesMetaZFC.Model.Forcing.InternalNameConstruction

/-! # 内部名称扩张的全分离模式

从源名称的闭支撑中分离出带权子名称，权重同时加强原成员系数并力迫原分离正文。
真值定理在两个方向上给出精确成员刻画。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)

local notation "E" => extension_l M hZF B R z U
include O hZF hU

theorem internal_separation_l {n} (φ : UnarySchema n) (η : Env E n) (A : (E).Domain) :
    ∃ C : (E).Domain, ∀ x : (E).Domain,
      x ∈ C ↔ x ∈ A ∧ Formula.satisfies (η.push x) φ.body := by
  obtain ⟨ρ, hρ⟩ := lift_env_l hZF η
  obtain ⟨t, ht, hA⟩ := value_name_l A
  obtain ⟨S, htS, hS⟩ := ht
  let δ := (((ρ.push t).push B).push R).push z
  let e : Fin (n + 1) → Term (n + 6) := Fin.cases (.bound 1) (fun i => .bound ⟨i.val + 6, by omega⟩)
  let ψ : BinarySchema (n + 4) := {
    body := .conj (source_m (.bound 3) (.bound 5) (.bound 1) (.bound 0))
      (force_at_m φ.body e (.bound 4) (.bound 3) (.bound 2) (.bound 0))
    freeClosed := by
      have he : ∀ i, (e i).freeSupport = [] := Fin.cases rfl (fun _ => rfl)
      simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, he, φ.freeClosed] }
  have hψ a p : ψ.denote δ a p ↔ Source_d M R t a p ∧ Forces_d M B R z φ.body (ρ.push a) p := by
    have he : (⟨fun i => (e i).eval ((δ.push a).push p), ((δ.push a).push p).free⟩ : Env M (n + 1)) = ρ.push a := by
      rw [Env.mk.injEq]
      constructor
      · funext i; exact Fin.cases rfl (fun _ => rfl) i
      · rfl
    simp only [BinarySchema.denote, ψ, Formula.satisfies_conj_iff, source_sat_l M hZF.1,
      force_at_sat_l, he]
    rfl
  obtain ⟨q, hq, _, he⟩ := name_comp_l M hZF ψ δ B S (fun s hs => ⟨S, hs, hS⟩)
  obtain ⟨C, hC⟩ := name_value_l (R := R) (z := z) (U := U) hq
  refine ⟨C, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨a, p, ha, hp, hax⟩ := (qval_mem_l O hZF hU hC).mp hx
    obtain ⟨_, _, ha⟩ := (he a p).mp ha
    obtain ⟨ha, hφ⟩ := (hψ a p).mp ha
    exact ⟨source_val_l O hZF hU hA hax ha hp,
      (forcing_truth_l O hZF hU φ.body φ.freeClosed (ρ.push a) (η.push x)
        (env_val_push_l hZF hρ hax)).mp ⟨p, hp, hφ⟩⟩
  · rintro ⟨hx, hφ⟩
    obtain ⟨a, c, ha, hc, hax⟩ := (qval_mem_l O hZF hU hA).mp hx
    have ht := formula_eval_l O hZF hU φ.body φ.freeClosed (ρ.push a) (η.push x)
      (env_val_push_l hZF hρ hax)
    obtain ⟨p, hp, hφ⟩ := ht.2.mpr hφ
    obtain ⟨b, hb, hbc, hbp⟩ := hU.directed c p hc hp
    have hb' := hU.proper b hb
    have hφb := ht.1.1 p b (hU.proper p hp).1 ⟨hb'.1, hb'.2, hbp⟩ hφ
    exact (qval_mem_l O hZF hU hC).mpr ⟨a, b, (he a b).mpr
      ⟨(supp_entry_l M hS htS ha).1, hb'.1, (hψ a b).mpr ⟨⟨c, ha, hbc⟩, hφb⟩⟩, hb, hax⟩

end YesMetaZFC.Model.Forcing.Internal
