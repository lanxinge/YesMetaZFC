import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Linear

/-! # 字典序最小元所用的实际投影与纤维

投影像由 KP 的 Δ₀ 替换产生，最小坐标的非空纤维由 Δ₀ 分离产生。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Po_min_d (R : M.Domain → M.Domain → Prop) (X : M.Domain) : Prop :=
  ∃ c, M.mem c X ∧ ∀ d, M.mem d X → c = d ∨ R c d

theorem po_ordinal_min_l (hKP : M.Models KP) {X : M.Domain}
    (ho : ∀ a, M.mem a X → M.IsOrdinal a) (hn : ∃ a, M.mem a X) : Po_min_d M.mem X := by
  obtain ⟨a, ha, hm⟩ := KP.mem_minimal_exists_d hKP hn
  refine ⟨a, ha, fun b hb => ?_⟩
  rcases Structure.IsOrdinal.trichotomy hKP.1 (ho a ha) (ho b hb) (KP.difference_exists_d hKP)
    (KP.intersection_exists_d hKP a b) with h | h | h
  · exact Or.inl (hKP.1.eq_of_same_members a b h)
  · exact Or.inr h
  · exact (hm b hb h).elim

theorem po_minfiber_l (hKP : M.Models KP) {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (X : M.Domain)
    (ht : ∀ c, M.mem c X → ∃ a, φ.toBinarySchema.denote ρ c a)
    (hu : ∀ c, M.mem c X → ∀ a b, φ.toBinarySchema.denote ρ c a → φ.toBinarySchema.denote ρ c b → a = b)
    {R : M.Domain → M.Domain → Prop}
    (hl : ∀ Y, (∀ a, M.mem a Y ↔ ∃ c, M.mem c X ∧ φ.toBinarySchema.denote ρ c a) → Po_min_d R Y) :
    ∃ a U, (∀ c, M.mem c U ↔ M.mem c X ∧ φ.toBinarySchema.denote ρ c a) ∧
      (∃ c, M.mem c U) ∧ ∀ c, M.mem c X → ∀ b, φ.toBinarySchema.denote ρ c b → a = b ∨ R a b := by
  obtain ⟨Y, hY⟩ := KP.d0_image_l hKP φ ρ X ht hu
  obtain ⟨a, ha, hm⟩ := hl Y hY
  let ψ : Delta0UnarySchema (n + 1) := {
    body := binary_pred_m φ.toBinarySchema (fun i => .bound ⟨i.val + 2, by omega⟩) .newest (.bound 1)
    freeClosed := by simp -implicitDefEqProofs
    delta0 := φ.delta0.bind_l _ }
  have hψ c : ψ.toUnarySchema.denote (ρ.push a) c ↔ φ.toBinarySchema.denote ρ c a := by
    simp only [UnarySchema.denote, ψ, binary_pred_sat_l]; rfl
  obtain ⟨U, hU⟩ := KP.separation_exists_d hKP ψ (ρ.push a) X
  have hf c : M.mem c U ↔ M.mem c X ∧ φ.toBinarySchema.denote ρ c a :=
    (hU c).trans (and_congr_right fun _ => hψ c)
  obtain ⟨c, hc, hca⟩ := (hY a).mp ha
  exact ⟨a, U, hf, ⟨c, (hf c).mpr ⟨hc, hca⟩⟩, fun d hd b hb => hm b ((hY b).mpr ⟨d, hd, hb⟩)⟩

theorem po_pair_bound_l {T p a b : M.Domain} (ht : M.TransitiveSet T) (hp : M.mem p T)
    (h : KPair_d M p a b) : M.mem a T ∧ M.mem b T := by
  have lift z (hz : z = a ∨ z = b) : M.mem z T := by
    obtain ⟨s, hs, hz⟩ := (kpair_union_l M h z).mpr hz
    exact ht s (ht p hp s hs) z hz
  exact ⟨lift a (Or.inl rfl), lift b (Or.inr rfl)⟩

def Po_proj_d (r : Bool) (T c a : M.Domain) : Prop :=
  ∃ b, M.mem b T ∧ match r with | true => KPair_d M c b a | false => KPair_d M c a b

def po_proj_s (r : Bool) : Delta0BinarySchema 1 where
  body := Formula.existsMem (.bound 2) (match r with
    | true => kpair0_m (.bound 2) .newest (.bound 1) | false => kpair0_m (.bound 2) (.bound 1) .newest)
  freeClosed := by cases r <;> simp -implicitDefEqProofs
  delta0 := .existsMem _ (by cases r <;> exact kpair0_delta_l ..)

theorem po_proj_sat_l (hE : Extensional M) (r : Bool) (ρ : Env M 1) (c a : M.Domain) :
    (po_proj_s r).toBinarySchema.denote ρ c a ↔ Po_proj_d r (ρ.bound 0) c a := by
  cases r <;> simp only [BinarySchema.denote, po_proj_s, Po_proj_d, Formula.satisfies_existsMem_iff, kpair0_sat_l hE] <;> rfl

theorem po_proj_unique_l (r : Bool) {T c a b : M.Domain} (ha : Po_proj_d r T c a) (hb : Po_proj_d r T c b) : a = b := by
  obtain ⟨x, _, hx⟩ := ha
  obtain ⟨y, _, hy⟩ := hb
  cases r
  · exact (kpair_injective_l M hx hy).1
  · exact (kpair_injective_l M hx hy).2

def Po_arg_d (i : Fin 3) (T c x : M.Domain) : Prop :=
  ∃ t, M.mem t T ∧ ∃ p, M.mem p T ∧ ∃ a, M.mem a T ∧ ∃ b, M.mem b T ∧ ∃ d, M.mem d T ∧
    KPair_d M c t p ∧ Rd_triple_d p a b d ∧ x = Fin.cases a (Fin.cases b (fun _ => d)) i

def po_arg_s (i : Fin 3) : Delta0BinarySchema 1 where
  body := Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <|
    Formula.existsMem (.bound 5) <| Formula.existsMem (.bound 6) <|
      .conj (kpair0_m (.bound 6) (.bound 4) (.bound 3)) <|
        .conj (rd_triple0_m (.bound 3) (.bound 2) (.bound 1) .newest)
          (Formula.extensionalEq (.bound 5) (Fin.cases (.bound 2) (Fin.cases (.bound 1) (fun _ => .newest)) i))
  freeClosed := by
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] <;> rfl
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (kpair0_delta_l ..) (.conj (rd_triple0_delta_l ..) (.atom _ _ _)))))))

theorem po_arg_sat_l (hE : Extensional M) (i : Fin 3) (ρ : Env M 1) (c a : M.Domain) :
    (po_arg_s i).toBinarySchema.denote ρ c a ↔ Po_arg_d i (ρ.bound 0) c a := by
  simp only [BinarySchema.denote, po_arg_s, Po_arg_d, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, kpair0_sat_l hE, rd_triple0_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rfl

theorem po_arg_unique_l (i : Fin 3) {T c x y : M.Domain} (hx : Po_arg_d i T c x) (hy : Po_arg_d i T c y) : x = y := by
  obtain ⟨t, _, p, _, a, _, b, _, d, _, hc, hp, hx⟩ := hx
  obtain ⟨s, _, q, _, a', _, b', _, d', _, hd, hq, hy⟩ := hy
  obtain ⟨_, rfl⟩ := kpair_injective_l M hc hd
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hp hq
  exact hx.trans hy.symm

theorem po_node_fields_l {T U c a b d : M.Domain} {k} (ht : M.TransitiveSet T) (hc : M.mem c T)
    (hn : Pc_node_d U k c a b d) :
    Pc_node_d T k c a b d ∧ ∀ i : Fin 3, Po_arg_d i T c (Fin.cases a (Fin.cases b (fun _ => d)) i) := by
  obtain ⟨t, _, p, _, hn, ⟨q, hq, hp⟩, he⟩ := hn
  have hb := po_pair_bound_l ht hc he
  have hd := po_pair_bound_l ht hb.2 hp
  have hf := po_pair_bound_l ht hd.2 hq
  exact ⟨⟨t, hb.1, p, hb.2, hn, ⟨q, hq, hp⟩, he⟩,
    fun i => ⟨t, hb.1, p, hb.2, a, hd.1, b, hf.1, d, hf.2, he, ⟨q, hq, hp⟩, rfl⟩⟩

end YesMetaZFC.SetTheory.InnerModel
