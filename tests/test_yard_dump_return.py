"""Regression checks for full yard can -> dump -> same yard."""
import os
import tempfile
import importlib

tmp = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(tmp, "yard_return.db")
os.environ["SECRET_KEY"] = "yard-return-test"
app = importlib.import_module("app")
app.init_db()
conn = app.get_db()
conn.execute("INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,yard_address,yard_city,created_at) VALUES (?,?,?,?,?,?,?,?)",
             ("Return Co","return-co","pro","active",10,"2545 Squadron Ct","Virginia Beach",app.now_ts()))
company = conn.execute("SELECT id FROM companies WHERE slug='return-co'").fetchone()["id"]
conn.commit()
conn.close()

def parsed(note, return_leg=""):
    return {"action":"YARD","address":"2545 Squadron Ct, Virginia Beach",
            "dump_leg":"HRRC","return_leg":return_leg,"notes":note,"assigned_can":"3063"}

out = app._ensure_yard_dump_return([parsed("take the empty container back to yard")], company)
assert out[0]["return_leg"] == "2545 Squadron Ct, Virginia Beach"
out = app._ensure_yard_dump_return([parsed("head to yard after dumping")], company)
assert not out[0]["return_leg"]
out = app._ensure_yard_dump_return([parsed("return container to yard", "Other Site")], company)
assert out[0]["return_leg"] == "Other Site"

stop = {"action":"Yard","customer_name":"Yard","dump_location":"HRRC",
        "return_destination":"2545 Squadron Ct, Virginia Beach","active_leg":"primary",
        "driver_status":""}
legs, active = app._cab_stop_legs(stop,"2545 Squadron Ct, Virginia Beach",{}, {})
assert [leg["key"] for leg in legs] == ["primary","dump","return"]
assert legs[2]["address"] == "2545 Squadron Ct, Virginia Beach"
print("PASS yard dump return")
