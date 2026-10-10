import YesMetaZFC.SetTheory.Collapse.Transport

/-! # 集合隶属子结构的 Σ₁ 见证保持

采用“存在量词加 Δ₀ 矩阵”的实际语法接口，允许任意有限参数。坍塌同构
逐参数传输这些见证；完整内部初等结构将在凝聚入口给出具体实例。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure S1_sub_d (X U : M.Domain) : Prop where
  subset : M.MemberSubset X U
  nonempty : Nonempty {x : M.Domain // M.mem x X}
  witness : ∀ (hX : Nonempty {x : M.Domain // M.mem x X}) (hU : Nonempty {x : M.Domain // M.mem x U}),
    ∀ {n} (φ : Delta0UnarySchema n) (ρ : Env (rt_model_l X hX) n) (η : Env (rt_model_l U hU) n),
      (∀ i, (ρ.bound i).val = (η.bound i).val) →
      ((∃ x, φ.toUnarySchema.denote ρ x) ↔ ∃ y, φ.toUnarySchema.denote η y)

theorem S1_sub_d.target_nonempty_l {X U : M.Domain} (h : S1_sub_d X U) : Nonempty {x : M.Domain // M.mem x U} :=
  h.nonempty.elim fun x => ⟨⟨x.val, h.subset x.val x.property⟩⟩

theorem S1_sub_d.refl_l {U : M.Domain} (hn : Nonempty {x : M.Domain // M.mem x U}) : S1_sub_d U U := by
  refine ⟨fun _ h => h, hn, fun _ _ _ φ ρ η he => ?_⟩
  exact exists_congr fun x => Formula.closed_env_l _ φ.freeClosed
    (funext (Fin.cases rfl (fun i => Subtype.ext (he i))))

theorem S1_sub_d.extensional_l (hE : Extensional M) {X U : M.Domain} (h : S1_sub_d X U)
    (hu : M.TransitiveSet U) : Mc_ext_d X := by
  intro a ha b hb same
  let N := rt_model_l X h.nonempty
  let V := rt_model_l U h.target_nonempty_l
  let φ : Delta0UnarySchema 2 := { body := Formula.extensionalEq (.bound 1) (.bound 2), delta0 := .atom _ _ _ }
  let ρ : Env N 2 := ⟨Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩), fun _ => ⟨a, ha⟩⟩
  let η : Env V 2 := ⟨Fin.cases ⟨a, h.subset a ha⟩ (fun _ => ⟨b, h.subset b hb⟩), fun _ => ⟨a, h.subset a ha⟩⟩
  have left : ∃ x, φ.toUnarySchema.denote ρ x := by
    refine ⟨⟨a, ha⟩, (Formula.satisfies_extensionalEq_iff _ _ _).mpr ?_⟩
    exact fun z => same z.val z.property
  obtain ⟨x, hx⟩ := (h.witness _ _ φ ρ η (fun i => by cases i using Fin.cases <;> rfl)).mp left
  have eq := (Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hE hu h.target_nonempty_l) _ _ _).mp hx
  exact congrArg Subtype.val eq

theorem Mc_iso_d.nonempty_l {X B F : M.Domain} (h : Mc_iso_d X B F)
    (hn : Nonempty {x : M.Domain // M.mem x X}) : Nonempty {x : M.Domain // M.mem x B} := by
  obtain ⟨x⟩ := hn
  obtain ⟨y, hy, _⟩ := h.function.2.1 x.val x.property
  exact ⟨⟨y, hy⟩⟩

/-- Σ₁ 存在见证的全域性沿初等子结构与实际坍塌图传输。 -/
theorem Mc_iso_d.total_pull_l {X U B F : M.Domain} (s : S1_sub_d X U) (h : Mc_iso_d X B F)
    (hB : Nonempty {x : M.Domain // M.mem x B}) {n} (φ : Delta0UnarySchema n)
    (ht : ∀ η : Env (rt_model_l U s.target_nonempty_l) n, ∃ y, φ.toUnarySchema.denote η y)
    (η : Env (rt_model_l B hB) n) : ∃ y, φ.toUnarySchema.denote η y := by
  obtain ⟨ρ, he⟩ := h.params_l s.nonempty hB η
  let ζ : Env (rt_model_l U s.target_nonempty_l) n :=
    ⟨fun i => ⟨(ρ.bound i).val, s.subset _ (ρ.bound i).property⟩,
      fun i => ⟨(ρ.free i).val, s.subset _ (ρ.free i).property⟩⟩
  have ex := (s.witness s.nonempty s.target_nonempty_l φ ρ ζ (fun _ => rfl)).mpr (ht ζ)
  exact (Formula.satisfies_exists_iff η φ.body).mp
    ((h.formula_l s.nonempty hB (.existsE φ.body)
      (by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed) ρ η he).mp
        ((Formula.satisfies_exists_iff ρ φ.body).mpr ex))

end YesMetaZFC.SetTheory
