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

theorem Cp0_d.value_l {A B C t f g v w x : M.Domain} (h : Cp0_d A B C t f g)
    (ht : Fn0_d A B t) (hf : Fn0_d B C f) (hw : Rd_entry_d v w t) :
    Rd_entry_d v x g ↔ Rd_entry_d w x f := by
  obtain ⟨w', hw', y, hy, htw, hfy, hgy⟩ := h.2 v (ht.bound_l hw).1
  have eq := ht.2.2 v (ht.bound_l hw).1 w' hw' w (ht.bound_l hw).2 htw hw
  subst w'
  exact ⟨fun hx => (h.1.2.2 v (h.1.bound_l hx).1 x (h.1.bound_l hx).2 y hy hx hgy).symm ▸ hfy,
    fun hx => (hf.2.2 w (ht.bound_l hw).2 x (hf.bound_l hx).2 y hy hx hfy).symm ▸ hgy⟩

theorem Cp0_d.assoc_l {A B C X t s u f g k : M.Domain}
    (ht : Fn0_d B A t) (hs : Fn0_d C B s) (hu : Cp0_d C B A s t u) (hf : Fn0_d A X f)
    (hg : Cp0_d B A X t f g) (hk : Cp0_d C B X s g k) : Cp0_d C A X u f k := by
  refine ⟨hk.1, fun v hv => ?_⟩
  obtain ⟨w, hw, hvw⟩ := hs.2.1 v hv
  obtain ⟨z, hz, hwz⟩ := ht.2.1 w hw
  obtain ⟨x, hx, hvx⟩ := hk.1.2.1 v hv
  exact ⟨z, hz, x, hx, (hu.value_l hs ht hvw).mpr hwz,
    (hg.value_l ht hf hwz).mp ((hk.value_l hs hg.1 hvw).mp hvx), hvx⟩

theorem Cp0_d.retarget_l {A B X Y t f g : M.Domain} (h : Cp0_d A B X t f g)
    (hf : Fn0_d B Y f) : Cp0_d A B Y t f g := by
  have bound v x (hx : Rd_entry_d v x g) : M.mem x Y := by
    obtain ⟨w, _, y, hy, _, hwy, hvy⟩ := h.2 v (h.1.bound_l hx).1
    exact (h.1.2.2 v (h.1.bound_l hx).1 x (h.1.bound_l hx).2 y hy hx hvy).symm ▸ (hf.bound_l hwy).2
  refine ⟨h.1.retarget_l bound, fun v hv => ?_⟩
  obtain ⟨w, hw, x, _, hvw, hwx, hvx⟩ := h.2 v hv
  exact ⟨w, hw, x, (hf.bound_l hwx).2, hvw, hwx, hvx⟩

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

/-- KP 内部直接生成恒等图，同时返回逐点读取方程。 -/
theorem fn0_identity_l (hKP : M.Models KP) (X : M.Domain) :
    ∃ q, Fn0_d X X q ∧ ∀ x y, Rd_entry_d x y q ↔ M.mem x X ∧ x = y := by
  let φ : Delta0BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest, delta0 := .atom _ _ _ }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => X⟩
  have sat x y : (S1_binary.of_delta0 φ).schema.denote ρ x y ↔ x = y :=
    (S1_binary.of_delta0_sat_l ..).trans (Formula.satisfies_extensionalEq_iff_eq hKP.1 ..)
  obtain ⟨q, fq, spec⟩ := s1_function_l hKP (S1_binary.of_delta0 φ) ρ X X
    (fun x _ => ⟨x, (sat x x).mpr rfl⟩)
    (fun x _ y z hy hz => ((sat x y).mp hy).symm.trans ((sat x z).mp hz))
    (fun x hx y hy => (sat x y).mp hy ▸ hx)
  exact ⟨q, fq, fun x y => (spec x y).trans (and_congr Iff.rfl (sat x y))⟩

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

/-- 恒等坐标重排在整个实际函数空间上也是恒等。 -/
theorem cp0_projection_id_l {n X D q p : M.Domain} (hD : ∀ f, M.mem f D → Fn0_d n X f)
    (hp : Fn0_d D D p) (hq : ∀ i j, Rd_entry_d i j q ↔ M.mem i n ∧ i = j)
    (hs : ∀ f g, Rd_entry_d f g p ↔ M.mem f D ∧ Cp0_d n n X q f g) :
    ∀ f g, Rd_entry_d f g p ↔ M.mem f D ∧ f = g := by
  have fixed f (hf : M.mem f D) : Rd_entry_d f f p := (hs f f).mpr ⟨hf, hD f hf, fun i hi => by
    obtain ⟨x, hx, hix⟩ := (hD f hf).2.1 i hi
    exact ⟨i, hi, x, hx, (hq i i).mpr ⟨hi, rfl⟩, hix, hix⟩⟩
  exact fun f g => ⟨fun h => ⟨(hp.bound_l h).1,
    hp.2.2 f (hp.bound_l h).1 f (hp.bound_l h).1 g (hp.bound_l h).2 (fixed f (hp.bound_l h).1) h⟩,
    fun ⟨hf, he⟩ => he ▸ fixed f hf⟩

/-- 坐标函数的复合诱导反向的实际投影复合。 -/
theorem cp0_projection_comp_l {m n l X D E F q s u p r t : M.Domain}
    (hq : Fn0_d m n q) (hs : Fn0_d n l s) (hu : Cp0_d m n l q s u)
    (hF : ∀ f, M.mem f F → Fn0_d l X f) (hp : Fn0_d E D p) (hr : Fn0_d F E r) (ht : Fn0_d F D t)
    (hP : ∀ f g, Rd_entry_d f g p → Cp0_d m n X q f g)
    (hR : ∀ f g, Rd_entry_d f g r → Cp0_d n l X s f g)
    (hT : ∀ f g, M.mem f F → Cp0_d m l X u f g → Rd_entry_d f g t) : Cp0_d F E D r p t := by
  refine ⟨ht, fun f hf => ?_⟩
  obtain ⟨g, hg, hfg⟩ := hr.2.1 f hf
  obtain ⟨k, hk, hgk⟩ := hp.2.1 g hg
  exact ⟨g, hg, k, hk, hfg, hgk, hT f k hf (Cp0_d.assoc_l hs hq hu (hF f hf) (hR f g hfg) (hP g k hgk))⟩

end YesMetaZFC.SetTheory.InnerModel
