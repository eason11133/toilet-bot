import { createClient } from "npm:@supabase/supabase-js@2.95.0";

const jsonHeaders = { "Content-Type": "application/json; charset=utf-8" };
const expectedLineChannelId = "2007674330";
// Replaced only in the deployed artifact. Never commit the production secret.
const backendSecret = "__CONSENT_BACKEND_SECRET__";

function reply(body: Record<string, unknown>, status = 200) {
  return new Response(JSON.stringify(body), { status, headers: jsonHeaders });
}

function adminClient() {
  const keys = JSON.parse(Deno.env.get("SUPABASE_SECRET_KEYS") || "{}");
  const key = keys.default || Deno.env.get("SUPABASE_SERVICE_ROLE_KEY") || "";
  return createClient(Deno.env.get("SUPABASE_URL") || "", key, {
    auth: { persistSession: false, autoRefreshToken: false },
  });
}

function hasBackendSecret(req: Request) {
  const supplied = req.headers.get("x-consent-backend-secret") || "";
  return backendSecret.length >= 32 && supplied === backendSecret;
}

async function verifiedLineProfile(accessToken: string) {
  const verifyUrl = new URL("https://api.line.me/oauth2/v2.1/verify");
  verifyUrl.searchParams.set("access_token", accessToken);
  const verify = await fetch(verifyUrl);
  const verified = await verify.json().catch(() => ({}));
  if (!verify.ok || String(verified.client_id || "") !== expectedLineChannelId) {
    return null;
  }
  const profileResponse = await fetch("https://api.line.me/v2/profile", {
    headers: { Authorization: `Bearer ${accessToken}` },
  });
  const profile = await profileResponse.json().catch(() => ({}));
  if (!profileResponse.ok || !profile.userId) return null;
  return {
    userId: String(profile.userId),
    displayName: String(profile.displayName || "").slice(0, 200),
  };
}

Deno.serve(async (req: Request) => {
  if (req.method !== "POST") return reply({ ok: false, code: "method_not_allowed" }, 405);
  let body: Record<string, unknown>;
  try {
    body = await req.json();
  } catch {
    return reply({ ok: false, code: "invalid_json" }, 400);
  }
  const action = String(body.action || "");
  const supabase = adminClient();

  if (action === "upsert") {
    const accessToken = String(body.accessToken || "");
    if (!accessToken || accessToken.length > 4096) {
      return reply({ ok: false, code: "invalid_access_token" }, 401);
    }
    const profile = await verifiedLineProfile(accessToken);
    if (!profile) return reply({ ok: false, code: "invalid_access_token" }, 401);
    const now = new Date().toISOString();
    const { error } = await supabase.from("consent_staging").upsert({
      user_id: profile.userId,
      agreed: body.agreed === true,
      display_name: profile.displayName,
      source_type: String(body.sourceType || "").slice(0, 50),
      user_agent: String(body.userAgent || "").slice(0, 500),
      consented_at: now,
      updated_at: now,
      synced_to_neon_at: null,
    }, { onConflict: "user_id" });
    if (error) return reply({ ok: false, code: "storage_failed" }, 503);
    return reply({ ok: true });
  }

  if (!hasBackendSecret(req)) return reply({ ok: false, code: "unauthorized" }, 401);

  if (action === "health") return reply({ ok: true });

  if (action === "check") {
    const userId = String(body.userId || "").slice(0, 128);
    if (!userId) return reply({ ok: false, code: "missing_user" }, 400);
    const { data, error } = await supabase.from("consent_staging")
      .select("agreed")
      .eq("user_id", userId)
      .maybeSingle();
    if (error) return reply({ ok: false, code: "storage_failed" }, 503);
    return reply({ ok: true, agreed: Boolean(data?.agreed) });
  }

  if (action === "list_unsynced") {
    const limit = Math.min(1000, Math.max(1, Number(body.limit || 500)));
    const { data, error } = await supabase.from("consent_staging")
      .select("user_id,agreed,display_name,source_type,user_agent,consented_at,updated_at")
      .is("synced_to_neon_at", null)
      .order("updated_at", { ascending: true })
      .limit(limit);
    if (error) return reply({ ok: false, code: "storage_failed" }, 503);
    return reply({ ok: true, rows: data || [] });
  }

  if (action === "mark_synced") {
    const ids = Array.isArray(body.userIds)
      ? body.userIds.map(String).filter(Boolean).slice(0, 1000)
      : [];
    if (!ids.length) return reply({ ok: false, code: "missing_users" }, 400);
    const { error } = await supabase.from("consent_staging")
      .update({ synced_to_neon_at: new Date().toISOString() })
      .in("user_id", ids);
    if (error) return reply({ ok: false, code: "storage_failed" }, 503);
    return reply({ ok: true, updated: ids.length });
  }

  return reply({ ok: false, code: "unknown_action" }, 400);
});
